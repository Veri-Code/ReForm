import re
import os
import json
import matplotlib.pyplot as plt
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading

from verl.utils.reward_score.dafny_oneshot_pure_remove_fulllog import *
from verl.utils.reward_score.condition_comparison_fixed import strip_specs_and_inject_asserts
from verl.inference.reward_score.spec_coverage import *
from verl.inference.reward_score.inference_reward import *
from verl.inference.plot import *


folder_names = [
    "/nas/shared/sys2/chefengdi/eval_log/3B/DLC_4nodes_3B_reward_naive_0513_v5/global_step_40",
    ]

def process_gt(llm_code,folder_name, index):
    gt_dataset_path = "/nas/shared/sys2/liyizhi/dafny_process/processed_data/rl_opt_5k_vanilla_pure_complex_and_hacking_remove_v3_train.json"
    gt_dataset = json.load(open(gt_dataset_path, 'r'))
    dir_path = os.path.join(folder_name, str(index))
    
    llm_first = llm_code.split('\n', 1)[0]

    gt_code = input_code = None
    for entry in gt_dataset:
        if entry['input'].split('\n', 1)[0] == llm_first:
            gt_code = entry['output']
            input_code = entry['input']
            break
    if gt_code is None:
        return None, None  # no match

    # match GT
    gt_out_path = os.path.join(dir_path, "gt.dfy")
    with open(gt_out_path, 'w') as f:
        f.write(gt_code)
        
    input_out_path = os.path.join(dir_path, "input.dfy")
    with open(input_out_path, 'w') as f:
        f.write(input_code)
    
    return gt_code, input_code

def process_single_index(folder_name, index, BoN=4):
    """Process a single index - this function will be run in parallel"""
    index_path = os.path.join(folder_name, str(index))
        
    filelists = os.listdir(index_path)
    # total_files = [x for x in filelists if x.endswith(".dfy") and x not in ["gt.dfy", "input.dfy"]]
    # print("Data at index: ", index, " has total files: ", len(total_files))
    # filelists = [int(x[:-4]) for x in filelists if x.endswith(".dfy") and x not in ["gt.dfy", "input.dfy"]]
        
    # file1 = min(filelists)
    # file2 = max(filelists)
    # sorted_filelists = sorted(filelists)
    for file in filelists:
      if file.endswith(".dfy") and file not in ["gt.dfy", "input.dfy"]:
        file1 = int(file[:-4])
        break

    step_num = len(filelists) // BoN

    # scores = {}
    # for step in range(step_num):
    #     scores[step] = {}
    #     for shot in range(BoN):
    #         scores[step][shot] = []
    
    if not os.path.exists(os.path.join(folder_name, str(index), "gt.dfy")):
        llm_code = open(os.path.join(folder_name, str(index), f"{file1}.dfy"), "r").read()
        gt_code, input_code = process_gt(llm_code, folder_name, index)
    else:
        gt_code = open(os.path.join(folder_name, str(index), "gt.dfy"), "r").read()

    if gt_code is None:
      print("gt_code is None")
      print("llm_code: ", llm_code)
      return [0] * 9

    file_path = os.path.join(folder_name, str(index), f"{file1}.dfy")
    if not os.path.exists(file_path):
        return [0] * 9
        
    llm_code = open(file_path, "r").read()
    llm_code = llm_code.replace("```dafny", "").replace("```", "")
    score = compute_subset_score(
        llm_code, 
        gt_code, 
        exp_name = 'test_score',
        index=index,
        output_dir="/nas/shared/sys2/chefengdi/eval_log/random_test/",
        eval_plot=True)
    # if score[3] == -1:
    #   print("llm_code: ", llm_code)
    #   print("gt_code: ", gt_code)
    #   gt_insert_code = strip_specs_and_inject_asserts(gt_code, llm_code, key="one_score")
    #   print("gt_insert_code: ", gt_insert_code)
    if score[8] == -1: 
      # print("llm_code: ", llm_code)
      # print("gt_code: ", gt_code)
      gt_insert_code = reinsert_gt_spec(gt_code, llm_code)
      # print("gt_insert_code: ", gt_insert_code)
    
    return score

def count_result_parallel(folder_name, max_workers=8):
    """Parallel version of count_result using ThreadPoolExecutor"""
    print(f"Processing folder: {folder_name} with {max_workers} workers")
    
    # Create a list of indices to process
    indices = list(range(6,12))  # You can adjust this range as needed
    
    processed_count = 0
    skipped_count = 0
    total_scores = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit all tasks
        future_to_index = {executor.submit(process_single_index, folder_name, index): index 
                          for index in indices}
        
        # Process completed tasks with progress bar
        with tqdm(total=len(indices), desc="Processing indices") as pbar:
            for future in as_completed(future_to_index):
                result = future.result()
                if result is not None:
                    processed_count += 1
                    total_scores.append(result)
                else:
                    skipped_count += 1
                pbar.update(1)
    
    # Since we only process one file per index and BoN=1, create simple structure
    final_scores = {}
    # Assuming single step (0) and single shot (0)
    final_scores[0] = {}
    final_scores[0][0] = total_scores
    
    print(f"SUMMARY: Successfully processed {processed_count} indices, skipped {skipped_count} indices out of {len(indices)} total")
    
    return final_scores


if __name__ == "__main__":
    # import argparse
    
    # parser = argparse.ArgumentParser(description='Process Dafny files with optional parallel processing')
    # parser.add_argument('--parallel', default=True, help='Use parallel processing')
    # parser.add_argument('--workers', type=int, default=8, help='Number of worker threads (default: 8)')
    
    # args = parser.parse_args()
    # cumulative_scores = {}
    # folder_names = [
    #   # "/nas/shared/sys2/chefengdi/dafny_full_log/fengdi_score_3grpo_5ksft_3B_specRefine_no_hacking_v3_0531_10pm",
    #   "/nas/shared/sys2/liyizhi/full_log/DLC_4nodes_3B_reward_naive_0513_v5",
    #   # "/nas/shared/sys2/chefengdi/dafny_full_log/fengdi_grpo_5ksft_3B_specRefine_reward_hacking_v3_0531_12pm",
    # ]
    # for folder_name in folder_names:
    #     print("folder_name: ", folder_name)
    #     exp_name = os.path.basename(folder_name) 
    #     cumulative_scores[exp_name] = {}
    #     print("exp_name: ", exp_name)
    #     total_scores = count_result_parallel(folder_name, max_workers=args.workers)

    code = """
class WebDriver {
  var isActive: bool
  var currentUrl: string
  constructor()
    ensures isActive
    ensures currentUrl == ""
  {
    isActive := true;
    currentUrl := "";
  }
}
class Screenshot {
  var path: string
  var timestamp: nat
  constructor(p: string, t: nat)
    ensures path == p
    ensures timestamp == t
  {
    path := p;
    timestamp := t;
  }
}
predicate StartsWith(s: string, prefix: string)
{
  |s| >= |prefix| && prefix <= s
}
function {:axiom} NatToString(n: nat): (result: string)
  ensures |result| > 0
method {:axiom} GetCurrentTimestamp() returns (timestamp: nat)
  ensures timestamp >= 0
method Sleep(seconds: nat)
method CaptureScreenshots(baseDir: string, maxScreenshots: nat) returns (screenshots: seq<Screenshot>)
  requires maxScreenshots > 0
  requires |baseDir| > 0
  ensures |screenshots| <= maxScreenshots
  ensures forall i :: 0 <= i < |screenshots| ==> StartsWith(screenshots[i].path, baseDir)
  ensures true
{
  var driver := new WebDriver();
  var counter: nat := 0;
  screenshots := [];
  while counter < maxScreenshots
    invariant 0 <= counter <= maxScreenshots
    invariant |screenshots| == counter
    invariant forall i :: 0 <= i < |screenshots| ==> StartsWith(screenshots[i].path, baseDir)
  {
    driver.currentUrl := "https://www.google.co.in/maps";
    var timestamp := GetCurrentTimestamp();
    var counterStr := NatToString(counter);
    var timestampStr := NatToString(timestamp);
    var filename := counterStr + timestampStr + ".png";
    var fullPath := baseDir + "/" + filename;
    var screenshot := new Screenshot(fullPath, timestamp);
    screenshots := screenshots + [screenshot];
    counter := counter + 1;
    Sleep(20);
  }
}
    """
    gt_code = """
      ```dafny
class WebDriver {
  var isActive: bool
  var currentUrl: string
  constructor()
    ensures isActive
    ensures currentUrl == ""
  {
    isActive := true;
    currentUrl := "";
  }
}
class Screenshot {
  var path: string
  var timestamp: nat
  constructor(p: string, t: nat)
    ensures path == p
    ensures timestamp == t
  {
    path := p;
    timestamp := t;
  }
}
predicate StartsWith(s: string, prefix: string)
{
  |s| >= |prefix| && prefix <= s
}
function {:axiom} NatToString(n: nat): (result: string)
  ensures |result| > 0
method {:axiom} GetCurrentTimestamp() returns (timestamp: nat)
  ensures timestamp > 0
method Sleep(seconds: nat)
  requires seconds > 0
method CaptureScreenshots(baseDir: string, maxScreenshots: nat) returns (screenshots: seq<Screenshot>)
  requires baseDir != ""
  requires maxScreenshots > 0
  ensures |screenshots| == maxScreenshots
  ensures forall i :: 0 <= i < |screenshots| ==>
    StartsWith(screenshots[i].path, baseDir)
{
  var driver := new WebDriver();
  var counter: nat := 0;
  screenshots := [];
  while counter < maxScreenshots
    invariant counter >= 0
    invariant counter <= maxScreenshots
    invariant driver.isActive
    invariant |screenshots| == counter
    invariant forall i :: 0 <= i < |screenshots| ==>
      StartsWith(screenshots[i].path, baseDir)
    decreases maxScreenshots - counter
  {
    driver.currentUrl := "https://www.google.co.in/maps";
    var timestamp := GetCurrentTimestamp();
    var counterStr := NatToString(counter);
    var timestampStr := NatToString(timestamp);
    var filename := counterStr + timestampStr + ".png";
    var fullPath := baseDir + "/" + filename;
    var screenshot := new Screenshot(fullPath, timestamp);
    screenshots := screenshots + [screenshot];
    counter := counter + 1;
    Sleep(20);
  }
}
```
"""
    spec_insert_code = strip_specs_and_inject_asserts(gt_code, code, key="one_score")
    print(spec_insert_code)
