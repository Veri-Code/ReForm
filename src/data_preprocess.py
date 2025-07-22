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

def make_prefix(dp):
    hints_removed = dp['input'].replace("```dafny", "").replace("```", "")
    ground_truth = dp['output']
    
    prefix = f"<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n\n{hints_removed}```<|im_end|>\n<|im_start|>assistant\n"

    return prefix



if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--local_dir', default='dataset2')
    args = parser.parse_args()
    
    raw_dataset = load_dataset("Veri-Code/ReForm-Python2Dafny-Dataset")["train"]

    # if use JSON style input, use the following codes
    # with open(train_json, 'r') as f:
    #     train_dataset = json.load(f)
    # raw_dataset = Dataset.from_list(train_dataset)

    data_source = 'dataset8k_pure_remove'
    TRAIN_SIZE = 4488
    TEST_SIZE = 512
    assert len(raw_dataset) >= TRAIN_SIZE + TEST_SIZE


    train_dataset = raw_dataset.select(range(TRAIN_SIZE))
    test_dataset = raw_dataset.select(range(TRAIN_SIZE, TRAIN_SIZE + TEST_SIZE))

    def make_map_fn(split):
        def process_fn(example, idx):
            question = make_prefix(example)
            solution = {
                "ground_truth": example['output'],                
                "hints_removed": example['input'].replace("```", "")
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

