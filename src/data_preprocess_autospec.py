import re
import os
from datasets import Dataset, load_from_disk, load_dataset
from random import randint, seed, choice
from typing import List, Tuple
from tqdm import tqdm
import sys
sys.path.append("..")
from verl.utils.hdfs_io import copy, makedirs
import argparse
import json
import numpy as np
from verl.utils.reward_score.condition_comparison_fixed import remove_singleline_specs, hint_remove
def remove_empty_lines(input_str):
    lines = input_str.split('\n')
    non_empty_lines = [line for line in lines if line.strip() != '']
    return '\n'.join(non_empty_lines)
def fix_input(input_):
    pattern = re.compile(r'\((\d+),\d+\): Error:')
    input_ = input_.replace("```dafny", "").replace("```", "")
    for j in range(10):

        with open("temp.dfy", "w") as f:
            f.write(input_)


        os.system("dafny resolve --allow-warnings temp.dfy > out.txt 2> /dev/null")

        with open("out.txt", "r") as f:
            output = f.read()
            # print(output)
            if "Dafny program verifier did not attempt verification" in output:
                break
            else:
                # if j == 9:
                    # print("index not solved:", idx)
                    # print(data["input"][idx])
                    # print("\n---------\n")
                    # print(input_)
                    # print("\n---------\n")
                    # print(output)
                    # print("\n---------\n")

                # print(idx)
                lines = input_.split('\n')
                # wrong_line = pattern.search(output).group(1)
                wrong_lines = pattern.findall(output)

                for wrong_line in wrong_lines:
                    # print(wrong_line)


                    lines[int(wrong_line)-1] = ""

                input_ = "\n".join(lines)
    return input_

def make_prefix(dp):

    # ground_truth = dp['gt_output']
    # input_ = dp["org_input"]

    ground_truth = dp["dafny"]
    input_ = hint_remove(ground_truth)

    hints_removed = remove_empty_lines(fix_input(input_))
    # hints_removed = dp['input'].replace("```dafny", "").replace("```", "")
    # ground_truth = dp['gt_output']
    
    prefix = f"<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n\n{hints_removed}```<|im_end|>\n<|im_start|>assistant\n"

    return prefix, hints_removed, ground_truth



if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--local_dir', default='dataset3')
    args = parser.parse_args()
    
    # raw_dataset = load_dataset("Veri-Code/ReForm-Python2Dafny-Dataset")["train"]

    # if use JSON style input, use the following codes
    train_json = "/mnt/workspace/liyizhi/dafny_process/DafnyAutoSpec/eval/dfyautospec_chain300_partial.json"
    train_json = "/mnt/workspace/liyizhi/dafny_process/DafnyAutoSpec/code_wspec/dfyautospec.json"
    with open(train_json, 'r') as f:
        train_dataset = json.load(f)
    raw_dataset = Dataset.from_list(train_dataset)

    data_source = 'dataset8k_pure_remove'
    # TRAIN_SIZE = 4488
    # TEST_SIZE = 512
    TRAIN_SIZE = 0
    TEST_SIZE = 300

    assert len(raw_dataset) >= TRAIN_SIZE + TEST_SIZE


    train_dataset = raw_dataset.select(range(TRAIN_SIZE))
    test_dataset = raw_dataset.select(range(TRAIN_SIZE, TRAIN_SIZE + TEST_SIZE))

    def make_map_fn(split):
        def process_fn(example, idx):
            question, ipt, gt = make_prefix(example)
            solution = {
                "ground_truth": gt,                
                "hints_removed": ipt
            }
            data = {
                "data_source": data_source,
                "prompt": [{
                    "role": "user",
                    "content": question,
                }],
                "ability": "code",
                "reward_model": {
                    "style": "rule",
                    "ground_truth": solution
                },
                "extra_info": {
                    'split': split,
                    'index': idx,
                }
            }
            return data
        return process_fn
    
    train_dataset = train_dataset.map(function=make_map_fn('train'), with_indices=True)
    test_dataset = test_dataset.map(function=make_map_fn('test'), with_indices=True)

    local_dir = args.local_dir

    train_dataset.to_parquet(os.path.join(local_dir, 'train.parquet'))
    test_dataset.to_parquet(os.path.join(local_dir, 'test.parquet'))

