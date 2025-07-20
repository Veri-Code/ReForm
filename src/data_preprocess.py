"""
Preprocess dataset for completing Dafny programs - given a piece of Dafny code, add certain lines of invariant, etc., to complete the program.
"""

import re
import os
from datasets import Dataset, load_from_disk
from random import randint, seed, choice
from typing import List, Tuple
from tqdm import tqdm
from verl.utils.hdfs_io import copy, makedirs
import argparse
import json
import numpy as np

COT_SYS_DAFNY = """You are a fommal verification expert specializing in Dafny. You will be given programing problems, and your job is to write a correct and fully annotated Dafny program.

You must only output the following structured blocks:
1. <Dafny> ...</Dafny> : Contains only valid Dafny code.
2. <Answer> ... </Answer> : Used **only when** you have written a complete, verified solution.
3. Never output anything outside of those tags.
4. If the program does not yet verify, wait for compiler feedback between turns.

The input may also include:
- <compiler> ...</compiler> blocks: These contain compiler messages to help you debug.
You may use them to revise your Dafny code in future <Dafny> blocks.

Once you are confident the programis complete and has passed verification, output an <Answer> block with a brief summary of your solution.

Always end your response at </Dafny> or </Answer>.
"""

COT_GEN_HINTS_FROM_BODY = """Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in coments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:
"""
def make_prefix(dp, template_type):
    hints_removed = dp['input'].replace("```dafny", "").replace("```", "")
    ground_truth = dp['output']
    # NOTE: also need to change reward_score/dafny_oneshot.py
    
    if template_type == 'base':
        """This works for any base model"""
        prefix = f"""Complete the following Dafny program. Add the necessary annotations to make the program able to be verified by Dafny. You should not use assume false or similar false expressions. Do not output think process to answer part, start directly by program you genereate. You can use the following hints to help you complete the program:
{hints_removed} Show your work in <think> </think> tags. And return the final answer in <answer> </answer> tags. For example, <answer>method...</answer>
Assistant: Let me solve this step by step.
<think>"""
    elif template_type == 'qwen-instruct':
        """This works for Qwen Instruct Models"""
        prefix = f"""<|im_start|>system\nYou are a helpful assistant. You first thinks about the reasoning process in the mind and then provides the user with the answer.<|im_end|>\n<|im_start|>user\nComplete the following Dafny program. Add the necessary annotations to make the program able to be verified by Dafny. You can use the following hints to help you complete the program:
{hints_removed} Show your work in <think> </think> tags. And return the final answer in <answer> </answer> tags.<|im_end|>\n<|im_start|>assistant\nLet me solve this step by step.\n<think>"""
    elif template_type == 'dafny_cot':
        prefix = f"""<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines.
        Show your middle progress in <think> </think> tags, And return the final answer in <answer>```dafny </answer> tags, DO NOT output you answer in <think></think>: return you answer in <ansewr></answer> tags. For example: <answer>```dafny method some_method ... ```</answer>. Below is the program: ```dafny\n\n{hints_removed}\n<|im_end|>\n<|im_start|>assistant\nLet me solve this step by step.\n<think> Well, """
    elif template_type == 'dafny_cot_vsft':
        prefix = f"<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n\n{hints_removed}```<|im_end|>\n<|im_start|>assistant\n"
    elif template_type == 'dafny_cot_wexample':
        example = "method append(a:array<int>, b:int) returns (c:array<int>)\n  ensures  a[..] + [b] == c[..]\n{\n  c := new int[a.Length+1];\n  var i:= 0;\n  while (i < a.Length)\n    invariant 0 <= i <= a.Length\n    invariant forall x :: 0 <= x < i ==> c[x] == a[x]\n  {\n    c[i] := a[i];\n    i:=i+1;\n  }\n  c[a.Length]:=b;\n}"
        prefix = f"""<|im_start|>system\nYou are an expert in dafny. You first thinks about the reasoning process in the mind and then provides the user with the answer.<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Here is an example of invariant: <example>{example}</example>. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines.
Show your work in <think> </think> tags. And return the final answer in <answer>```dafny </answer> tags, DO NOT output you answer in <think></think>: return you answer in <ansewr></answer> tags. For example: <answer>```dafny method some_method ... ```</answer>.  Below is the program: ```dafny\n\n{hints_removed}\n<|im_end|>\n<|im_start|>assistant\nLet me solve this step by step.\n<think> Well, """
    elif template_type == "dafny_cot_woexample":
        prefix = f"""<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines.
        Show your middle progress in <think> </think> tags, And return the final answer in <answer>```dafny </answer> tags, DO NOT output you answer in <think></think>: return you answer in <ansewr></answer> tags. For example: <answer>```dafny method some_method ... ```</answer>. Below is the program: ```dafny\n\n{hints_removed}\n\n<|im_end|>\n<|im_start|>assistant\nLet me solve this step by step.\n<think> Well, """
    elif template_type == "sft":
        prefix = f"<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n\n{hints_removed}```<|im_end|>\n<|im_start|>assistant\n"
    elif template_type == "cot_multi":
        prefix = f"""
<|im_start|>system
You are a fommal verification expert specializing in Dafny. You will be given programing problems, and your job is to write a correct and fully annotated Dafny program.\n\nYou must only output the following structured blocks:\n1. <Dafny> ...</Dafny> : Contains only valid Dafny code.\n2. <Answer> ... </Answer> : Used **only when** you have written a complete, verified solution.\n3. Never output anything outside of those tags.\n4. If the program does not yet verify, wait for compiler feedback between turns.\n\nThe input may also include:\n- <compiler> ...</compiler> blocks: These contain compiler messages to help you debug.\nYou may use them to revise your Dafny code in future <Dafny> blocks.\n\nOnce you are confident the programis complete and has passed verification, output an <Answer> block with a brief summary of your solution.\n\nAlways end your response at </Dafny> or </Answer>.\n
<|im_end|>
<|im_start|>user
Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in coments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n
<Dafny>
{hints_removed}
</Dafny>
<|im_end|>
<|im_start|>assistant
<Dafny>
"""
    elif template_type == "cot_multi2":
        prefix = f"""<|im_start|>system\n{COT_SYS_DAFNY}\n<|im_end|>\n<|im_start|>user\n{COT_GEN_HINTS_FROM_BODY}\n<Dafny>\n{hints_removed}\n</Dafny><|im_end|>\n<|im_start|>assistant\n"""
    elif template_type == "code_cot":
        prefix = f"""
        <|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n{hints_removed}\n```<|im_end|>\n<|im_start|>assistant\n"""
    return prefix



if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    # parser.add_argument('--org_dataset', type=str, default='TinyZero_Dafny_jz_workdir/TinyZero_Dafny-master/examples/data_preprocess/dafny_annotation.py')
    parser.add_argument('--local_dir', default='dataset5k_v3_for_code_cot')
    parser.add_argument('--hdfs_dir', default=None)
    # parser.add_argument('--train_size', type=int, default=631)
    # parser.add_argument('--test_size', type=int, default=100)
    # parser.add_argument('--template_type', type=str, default='dafny_cot_woexample')
    parser.add_argument('--template_type', type=str, default='sft')

    args = parser.parse_args()

    # train_json = "/nas/shared/sys2/liyizhi/dafny_process/processed_data/0325_8k1_new_vanilla_pure_remove_rl.json"
    # test_json = "/nas/shared/sys2/liyizhi/dafny_process/processed_data/0325_8k1_new_vanilla_pure_remove_dev.json"
    train_json = "/nas/shared/sys2/liyizhi/dafny_process/processed_data/rl_opt_5k_vanilla_pure_complex_and_hacking_remove_v3_train.json"
    # test_json = ""

    with open(train_json, 'r') as f:
        train_dataset = json.load(f)
    # with open(test_json, 'r') as f:
    #     test_dataset = json.load(f)

    # convert List into Dataset
    raw_dataset = Dataset.from_list(train_dataset)
    # test_dataset = Dataset.from_list(test_dataset)

    data_source = 'dataset8k_pure_remove'
    # TRAIN_SIZE = args.train_size
    # TEST_SIZE = args.test_size

    # raw_dataset = load_from_disk(args.org_dataset)

    # print(len(raw_dataset))
    # exit()
    TRAIN_SIZE = 4488
    TEST_SIZE = 512
    assert len(raw_dataset) >= TRAIN_SIZE + TEST_SIZE

    # fix the seed
    # seed = 42
    # set_seed(seed)

    train_dataset = raw_dataset.select(range(TRAIN_SIZE))
    test_dataset = raw_dataset.select(range(TRAIN_SIZE, TRAIN_SIZE + TEST_SIZE))

    def make_map_fn(split):
        def process_fn(example, idx):
            question = make_prefix(example, template_type=args.template_type)
            solution = {
                # "ground_truth": example['output'],
                "ground_truth": example['output'].split("<Answer>")[1].split("</Answer>")[0],                
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
    # hdfs_dir = args.hdfs_dir

    train_dataset.to_parquet(os.path.join(local_dir, 'train.parquet'))
    test_dataset.to_parquet(os.path.join(local_dir, 'test.parquet'))

    # if hdfs_dir is not None:
    #     makedirs(hdfs_dir)
    #     copy(src=local_dir, dst=hdfs_dir) 
