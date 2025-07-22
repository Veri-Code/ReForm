import re
import os
import matplotlib.pyplot as plt
import numpy as np
import seaborn as sns
import shutil
from tqdm import tqdm
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading

from verl.utils.reward_score.naive_reward import *
from verl.inference.reward_score.spec_coverage import *
from verl.utils.reward_score.condition_comparison_fixed import strip_specs_and_inject_asserts
from verl.inference.reward_score.inference_reward import compute_score_with_log, execute_diff_location, compute_subset_score

from verl.inference.plot import *


"""
IF running training result: change BoN to 1 and change exp_name to the basename of the folder_name
"""

# Thread-safe lock for printing and shared data
print_lock = threading.Lock()

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

    # # match GT
    # gt_out_path = os.path.join(dir_path, "gt.dfy")
    # with open(gt_out_path, 'w') as f:
    #     f.write(gt_code)
        
    # input_out_path = os.path.join(dir_path, "input.dfy")
    # with open(input_out_path, 'w') as f:
    #     f.write(input_code)
    
    return gt_code, input_code

def process_single_index(folder_name, index, BoN=1):
    """Process a single index - this function will be run in parallel"""
    index_path = os.path.join(folder_name, str(index))
        
    filelists = os.listdir(index_path)
    total_files = [x for x in filelists if x.endswith(".dfy") and x not in ["gt.dfy", "input.dfy"]]
    filelists = [int(x[:-4]) for x in filelists if x.endswith(".dfy") and x not in ["gt.dfy", "input.dfy"]]
        
    file1 = min(filelists)
    file2 = max(filelists)
    if not os.path.exists(os.path.join(folder_name, str(index), "gt.dfy")):
        llm_code = open(os.path.join(folder_name, str(index), f"{file1}.dfy"), "r").read()
        gt_code, input_code = process_gt(llm_code, folder_name, index)
    else:
        gt_code = open(os.path.join(folder_name, str(index), "gt.dfy"), "r").read()

    sorted_filelists = sorted(filelists)

    step_num = len(filelists) // BoN

    scores = {}
    for step in range(step_num):
        scores[step] = {}
        for shot in range(BoN):
            scores[step][shot] = []
    for idx, file in enumerate(sorted_filelists):
        scores[idx//BoN][idx%BoN]=[0] * 9

    if gt_code is None:
        return scores
    
    count = 0

    for idx, file in enumerate(sorted_filelists):
        file_path = os.path.join(folder_name, str(index), f"{file}.dfy")
        if not os.path.exists(file_path):
            continue
            
        llm_code = open(file_path, "r").read()
        llm_code = llm_code.replace("```dafny", "").replace("```", "")
        if idx//BoN >= step_num:
            continue
        scores[idx//BoN][idx%BoN]= compute_subset_score(
            llm_code, 
            gt_code, 
            exp_name = 'test_score',
            index = index, 
            output_dir="/nas/shared/sys2/liyizhi/folder-0709/eval_log/eval_plot_2/",
            eval_plot=True
            )
        # print(scores[idx//BoN][idx%BoN])
        # # # delete all files in the folder
    if scores[idx//BoN][idx%BoN][8] != 1:
        delete_dir = os.path.join("/nas/shared/sys2/liyizhi/folder-0709/eval_log/eval_plot_2/", str(index))
        for file in os.listdir(delete_dir):
            if os.path.isdir(os.path.join(delete_dir, file)):
                shutil.rmtree(os.path.join(delete_dir, file))
            else:
                os.remove(os.path.join(delete_dir, file))
    return scores

def count_result_parallel(folder_name,BoN, max_workers=8):
    """Parallel version of count_result using ThreadPoolExecutor"""
    print(f"Processing folder: {folder_name} with {max_workers} workers")
    
    # Create a list of indices to process
    # indices = list(range(512))  # You can adjust this range as needed
    indices = list(range(300))
    processed_count = 0
    skipped_count = 0
    total_scores = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit all tasks
        future_to_index = {executor.submit(process_single_index, folder_name, index, BoN): index 
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
    
    print(f"SUMMARY: Successfully processed {processed_count} indices, skipped {skipped_count} indices out of {len(indices)} total")
    
    final_scores = {}
    step_num = len(total_scores[0].keys()) 
    # step_num = 40
    key = list(total_scores[0].keys())[0]
    shot_num = len(total_scores[0][key].keys()) 
    for step in range(step_num):
        final_scores[step*2+2] = {}
        for shot in range(shot_num):
            final_scores[step*2+2][shot+1] = []

    if total_scores:  # Only process if we have results
        for step in range(step_num):
            for shot in range(shot_num):
                final_scores[step*2+2][shot+1] = []
                for result in total_scores:
                    final_scores[step*2+2][shot+1].append(result[step][shot])
    return final_scores


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='Process Dafny files with optional parallel processing')
    parser.add_argument('--parallel', default=True, help='Use parallel processing')
    parser.add_argument('--workers', type=int, default=8, help='Number of worker threads (default: 8)')
    
    parser.add_argument('--folder_names', nargs='+', required=True, help='List of folder names')

    args = parser.parse_args()
    cumulative_scores = {}

    folder_names = args.folder_names


    BoN = 1
    max_step_num =0 
    local_dir = "eval_log/"
    import datetime

    x  = datetime.datetime.now()
    date = [str(x.month),str(x.day),"hour",str(x.hour)]
    date = '-'.join(date)
    score_dir = os.path.join(local_dir, f"scores_{date}")
    if not os.path.exists(score_dir):
        os.makedirs(score_dir)

    for folder_name in folder_names:
        print("folder_name: ", folder_name)
        # exp_name = os.path.basename(os.path.dirname(folder_name)) + '/'+os.path.basename(folder_name) # parent of the basename is the exp_name
        exp_name = os.path.basename(folder_name)

        """
        IF running training result: change BoN to 1 and change exp_name to the basename of the folder_name
        change gloabl steps tp [0,2,]
        """

        cumulative_scores[exp_name] = {}
        print("exp_name: ", exp_name)
        total_scores = count_result_parallel(folder_name,BoN=BoN, max_workers=args.workers)
        
        step_num = len(total_scores.keys())
        max_step_num = max(step_num, max_step_num)
        num_key = list(total_scores.keys())[0]
        shot_num = len(total_scores[num_key].keys())
        print(f"step_num: {step_num}, shot_num: {shot_num}")
        print(f"total_scores keys: {list(total_scores.keys())}")
        print(f"total_scores[0] keys: {list(total_scores[num_key].keys())}")

        # cum_global_steps = [2]
        cum_global_steps = range(2, step_num*2+2,2)
        
        cumulative_scores[exp_name]['cumulative_results'] = compute_cumulative_binary_scores(
                total_scores, cum_global_steps, range(1, shot_num+1)
        )

        # save the cumulative scores
        cumluative_scores_copy = cumulative_scores[exp_name].copy()
        for step_key in cumluative_scores_copy['cumulative_results'].keys():
            for shot_key in cumluative_scores_copy['cumulative_results'][step_key].keys():
                score_list=cumluative_scores_copy['cumulative_results'][step_key][shot_key]
                if isinstance(score_list, np.ndarray):
                    cumluative_scores_copy['cumulative_results'][step_key][shot_key] = score_list.tolist()
        with open(os.path.join(score_dir, f"{exp_name}_scores_{date}.json"), "w") as f:
            json.dump(cumluative_scores_copy, f)
    
    exit()

    if "saves" in cumulative_scores:
        reordered_results = {}
        for exp_name in cumulative_scores: 
            if exp_name == "saves":
                continue  # We'll handle sft_ckpt separately
            
            reordered_results[exp_name] = {}
            reordered_results[exp_name]['cumulative_results'] = {}
            reordered_results[exp_name]['cumulative_results'][0] = cumulative_scores['saves']['cumulative_results'][2].copy()
            for step_key in cumulative_scores[exp_name]['cumulative_results'].keys():
                reordered_results[exp_name]['cumulative_results'][step_key] = cumulative_scores[exp_name]['cumulative_results'][step_key].copy()
        cumulative_scores = reordered_results

    # print(cumulative_scores)
    # global_steps = [0,2]
    global_steps = range(0,max_step_num*2+2,2)
        
    plot_dir = os.path.join(local_dir, f"plots_{date}")
    if not os.path.exists(local_dir):
        os.makedirs(local_dir)
    if not os.path.exists(plot_dir):
        os.makedirs(plot_dir)
    print(f"Plotting with step_num: {step_num}, shot_num: {shot_num}")
    print(f"Global steps: {list(global_steps)}")
    print(f"Shot numbers: {list(range(1, shot_num+1))}")
    plot_scores(cumulative_scores, global_steps, range(1, shot_num+1), plot_dir)

    
    def bench():

        # for exp_name in cumulative_scores:
        #     for step_key in cumulative_scores[exp_name]['cumulative_results'].keys():
        #         for shot_key in cumulative_scores[exp_name]['cumulative_results'][step_key].keys():
        #             score_list=cumulative_scores[exp_name]['cumulative_results'][step_key][shot_key]
        #             if isinstance(score_list, np.ndarray):
        #                 cumulative_scores[exp_name]['cumulative_results'][step_key][shot_key] = score_list.tolist()

        # with open(os.path.join(plot_dir, "scores.json"), "w") as f:
        #     json.dump(cumulative_scores, f)
    
        def plot_bench(plot_dir):
            exp_names = [
            "3B_prevent_hacking_kl0_lr1e-5_BoN16",
            "3B_prevent_hacking_kl005_lr1e-5_BoN32",
            "DLC_4nodes_3B_reward_naive_0609_v5",
            ]
            cumulative_scores = json.load(open(os.path.join(plot_dir, "scores.json"), "r"))
            reordered_cumulative_scores = {}
            for exp in exp_names:
                reordered_cumulative_scores[exp] = {}
                reordered_cumulative_scores[exp]['cumulative_results'] = {}
                for exp_name in cumulative_scores:
                    if exp in exp_name:
                        # reordered_cumulative_scores[exp][0][shot_key] = cumulative_scores[exp_name]['cumulative_results']['0'][shot_key]
                        step = int(exp_name.split('_')[-1])
                        reordered_cumulative_scores[exp]['cumulative_results'][0] = {}
                        reordered_cumulative_scores[exp]['cumulative_results'][step] = {}
                        for shot_key in cumulative_scores[exp_name]['cumulative_results']['2'].keys():
                            reordered_cumulative_scores[exp]['cumulative_results'][0][shot_key] = cumulative_scores[exp_name]['cumulative_results']['0'][shot_key]
                            reordered_cumulative_scores[exp]['cumulative_results'][step][shot_key] = cumulative_scores[exp_name]['cumulative_results']['2'][shot_key]
            return reordered_cumulative_scores

        local_dir = "eval_log/"
        plot_dir = os.path.join(local_dir, "plots")
        if not os.path.exists(local_dir):
            os.makedirs(local_dir)
        if not os.path.exists(plot_dir):
            os.makedirs(plot_dir)
        
        reordered_cumulative_scores = plot_bench(plot_dir)
        global_steps = [0,10,20,30,40,50,60]
        shot_num = 8
        plot_scores(reordered_cumulative_scores, global_steps, range(1, shot_num+1), plot_dir)

        shots_output_dir = os.path.join('eval_log/3B_log_compare/round_5', "shots_comparison/")
        # print(f"Target steps for shots plot: [2,5,9]")
        # print(f"Available steps: {list(range(step_num))}")
        plot_scores_vs_shots(reordered_cumulative_scores, global_steps, range(1,shot_num+1), shots_output_dir,target_steps=[0,20,40])

    # processed_data = {
    #     'exp_results': cumulative_scores,
    #     'global_steps': range(step_num),
    #     'shot_numbers': range(shot_num)
    # }
    # processed_data_path = os.path.join(plot_dir, exp_names[0], 'processed_data.npy')
    # os.makedirs(os.path.dirname(processed_data_path), exist_ok=True)
    # np.save(processed_data_path, processed_data)

#     code = """
# class FileSystem {
#   var contents: map<string, seq<string>>
#   constructor()
#     ensures contents.Keys == {}
#   {
#     contents := map[];
#   }
#   method ReadLines(filename: string) returns (lines: seq<string>)
#     requires filename in contents
#     ensures lines == contents[filename]
#   {
#     lines := contents[filename];
#   }
#   method WriteLines(filename: string, data: seq<string>)
#     modifies this
#     ensures contents == old(contents)[filename := data]
#   {
#     contents := contents[filename := data];
#   }
# }
# method CreateComboList(usernames: seq<string>, passwords: seq<string>) 
#   returns (combos: seq<string>)
#   requires |usernames| == |passwords| 
#   ensures |combos| == |usernames| 
# {
#   var minLength := if |usernames| < |passwords| then |usernames| else |passwords|;
#   combos := [];
#   var i := 0;
#   while i < minLength
#     invariant 0 <= i <= minLength
#     invariant |combos| == i
#   {
#     combos := combos + [usernames[i] + ":" + passwords[i]];
#     i := i + 1;
#   }
# }
# method Main(fs: FileSystem, usernameFile: string, passwordFile: string, outputFile: string)
#   modifies fs
#   requires usernameFile in fs.contents && passwordFile in fs.contents
#   requires |fs.contents[usernameFile]| == |fs.contents[passwordFile]| 
# {
#   var usernames := fs.ReadLines(usernameFile);
#   var passwords := fs.ReadLines(passwordFile);
#   var combos := CreateComboList(usernames, passwords);
#   fs.WriteLines(outputFile, combos);
# }
#     """
#     gt_code = """
#     ```dafny
# class FileSystem {
#   var Valid: set<string>
#   var contents: map<string, seq<string>>
#   constructor()
#     ensures Valid == {}
#     ensures contents == map[]
#   {
#     Valid := {};
#     contents := map[];
#   }
# }
# class DataPipeline {
#   var fs: FileSystem
#   var currentFile: string
#   constructor()
#     ensures fresh(fs)
#   {
#     fs := new FileSystem();
#     currentFile := "";
#   }
#   method ProcessItem<T>(item: T, spiderName: string) returns (success: bool)
#     modifies fs
#     requires currentFile in fs.Valid
#     requires spiderName != ""
#     requires currentFile in fs.contents.Keys
#     ensures currentFile in fs.contents.Keys
#     ensures success ==> |fs.contents[currentFile]| == old(|fs.contents[currentFile]|) + 1
#     ensures !success ==> fs.contents == old(fs.contents)
#     ensures fs.Valid == old(fs.Valid)
#     ensures fs.contents.Keys == old(fs.contents.Keys)
#   {
#     var itemStr := spiderName + ": " + "ItemData";
#     var oldContents := fs.contents[currentFile];
#     fs.contents := fs.contents[currentFile := oldContents + [itemStr]];
#     success := true;
#   }
# }
# ```
# """
#     output_dir = "/nas/shared/sys2/chefengdi/eval_log/eval_plot/test"
#     gt_insert_code = strip_specs_and_inject_asserts(gt_code, code, key="one_score",output_file=output_dir) 
#     print(gt_insert_code)
#     one_score_dict = execute_diff_location("dafny verify", "dfy", gt_insert_code, timeout_sec=30, index=10, exp_name='test', output_dir=output_dir)
#     if 'parse errors detected' in one_score_dict["out"] or 'resolution/type error' in one_score_dict["out"]:
#         # print("DEBUG- one_score_dict['out']: ", one_score_dict["out"])
#         print("parse errors detected")
#         print(one_score_dict["out"])
#     else:
#         errors = one_score_dict["out"].count("assertion might not hold")
#         func_errors = one_score_dict["out"].count("a postcondition could not be proved on this return path")
#         strong = errors==0
#         func_strong = func_errors==0
#         if gt_insert_code.count("assert")>0 or gt_insert_code.count("ensures")>0:
#             score = int(strong * func_strong)
#         else:
#             score = -1
#         print("score: ", score)