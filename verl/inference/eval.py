#!/usr/bin/env python3
"""
inference.py

Single GPU inference over an RLHFDataset.
"""

import torch
from pprint import pprint
from omegaconf import OmegaConf
import hydra
import os
import json
from tensordict import TensorDict
from concurrent.futures import ProcessPoolExecutor, as_completed
from functools import partial
from tqdm import tqdm

from verl import DataProto
from verl.utils.dataset.rl_dataset import RLHFDataset, collate_fn
from torchdata.stateful_dataloader import StatefulDataLoader
from verl.inference.reward_score.inference_reward import compute_subset_score
from verl.inference.model_utils.models import QwenModel
from verl.inference.model_utils.llm_inference import LLMInference
from verl.inference.model_utils.SampleItems import SampleItem, SampleItemList
from verl.utils.reward_score.naive_reward import *

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def prepare_llm_output(inputs,llm_output, batch, tokenizer):
    """
    Prepare LLM output by combining prompt and response into a single sequence.
    For each pair of (input_text, response), extracts Dafny code and combines them.
    
    Args:
        llm_output: List of model outputs
        batch: Batch data containing input information
        tokenizer: Tokenizer for encoding/decoding text
    
    Returns:
        list: List of strings where each string is input_text combined with its corresponding Dafny code
    """
    # # Get prompt ids from batch and decode them
    # prompt_ids_list = batch['input_ids']
    # input_texts = []
    # for i, prompt_ids in enumerate(prompt_ids_list):
    #     full_decoded_text = tokenizer.decode(prompt_ids)
    #     # Find the second occurrence of <|im_start|>system
    #     first_pos = full_decoded_text.find("<|im_start|>system")
    #     if first_pos != -1:
    #         decoded_text = full_decoded_text[first_pos:].strip()
    #     else:
    #         decoded_text = full_decoded_text
            
    #     input_texts.append(decoded_text)
    #     # print(f"\nDEBUG: Extracted Input prompt:\n{decoded_text}")
    
    # Process each response and combine with corresponding input text
    combined_outputs = []
    for input_text, response in zip(inputs, llm_output):
        # dafny_code = ""
        # Convert response to string if it's not already
        response_text = str(response) if not isinstance(response, str) else response
        # print(f"\nDEBUG: Extracted Dafny code:\n{dafny_code}")
        # Combine input text with this response's Dafny code
        combined_text = input_text + "\n" + response_text
        combined_outputs.append(combined_text)
    
    return combined_outputs

def save_inference_outputs(all_outputs, all_ids, all_scores, exp_name, ground_truth=None, save=False, output_dir=None):
    """Save inference outputs in a structured way."""
    if output_dir is None:
        raise ValueError("output_dir must be provided")
        
    os.makedirs(os.path.join(output_dir, exp_name), exist_ok=True)
    
    output_data = {}
    num_shots = len(all_scores[0]) if all_scores else 0
    print(f"num_shots: {num_shots}")
    
    for i, (sample_id, outputs, scores) in enumerate(zip(all_ids, all_outputs, all_scores)):
        output_data[str(sample_id)] = {
            "sample_id": sample_id,
            "shots": [],
            "ground_truth": ground_truth[i] if ground_truth is not None else None
        }
        
        for shot_idx in range(num_shots):
            shot_data = {
                "shot_number": shot_idx + 1,
                # "output": outputs,
                "score": scores[shot_idx]  # Keep the score as is, don't convert to float
            }
            output_data[str(sample_id)]["shots"].append(shot_data)
    
    if save:
        output_json_path = os.path.join(output_dir, exp_name, "all_results.json")
        with open(output_json_path, 'w', encoding='utf-8') as f:
            json.dump(output_data, f, indent=2, ensure_ascii=False)
    
    return output_data

def compute_score_parallel(input_tuple):
    """Helper function for parallel score computation."""
    solution_str, ground_truth, index, exp_name, version, output_dir = input_tuple
    return compute_subset_score(
        solution_str=solution_str,
        ground_truth=ground_truth,
        index=index,
        exp_name=exp_name,
        version=version,
        output_dir=output_dir,
        eval_plot=False,
        inference=True,
    )

class EvalRunner:
    """Class for running evaluation with LLM inference."""
    
    def __init__(self):
        self.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    
    def run(self, config):
        # Print and resolve config
        # print("DEBUG ------------------------------")
        # pprint(OmegaConf.to_container(config, resolve=True))
        OmegaConf.resolve(config)

        print("config.model.get('path','./')", config.model.get('path','./'))
        exp_name = config.trainer.experiment_name

        # Get model path
        model_path = config.model.get('path','./')
        
        # Get tensor parallel size from config
        tensor_parallel_size = config.get('parallel_processing', {}).get('tensor_parallel_size', 1)
        gpu_memory_utilization = config.get('parallel_processing', {}).get('gpu_memory_utilization', 0.8)
        print(f"Using tensor_parallel_size: {tensor_parallel_size}, gpu_memory_utilization: {gpu_memory_utilization}")
        
        # Initialize model with multi-GPU support
        model = QwenModel(
                model_path, 
                tensor_parallel_size=tensor_parallel_size,
                gpu_memory_utilization=gpu_memory_utilization
            )
        print(model_path, " Model loaded successfully")
        # Initialize LLMInference
        llm_inference = LLMInference(
            model,
            batch_size=config.data.get('batch_size', 32),
            prompt_type=config.get('prompt_type', 'sft'),
        )

        # # Process parquet file and run inference
        input_file = config.data.path

        # # Create output directory if it doesn't exist
        # os.makedirs(config.trainer.output_dir, exist_ok=True)
        # # Generate output file path in the output directory
        # output_file = os.path.join('/nas/shared/sys2/chefengdi/dafny_full_log/', f"{config.data.get('prompt_type', 'sft')}_{os.path.basename(input_file)}")
        # modified_file, inference_results = llm_inference.process_parquet_and_run(
        #     input_file,
        #     output_file=output_file,  # Pass the output file path
        #     generation_config=config.rollout,
        #     shot_number=config.rollout.get('shot_number', 1),
        #     prompt_type=config.data.get('prompt_type', 'sft')  # Pass the prompt type
        # )

        # # print(f"inference_results: {inference_results}")
        # print("DEBUG: inference_results")
        # print(f"inference_results: {inference_results[:2]}")
        # print("DEBUG: len(inference_results[0])", len(inference_results[0]))
        # print("-"*100)

        # Build validation DataLoader
        val_dataset = RLHFDataset(
            parquet_files=input_file,
            tokenizer=llm_inference.model.tokenizer,
            processor=llm_inference.model.processor,
            prompt_key=config.data.prompt_key,
            image_key=config.data.get('image_key', 'images'),
            max_prompt_length=config.rollout.max_prompt_length,
            return_raw_chat=config.data.get('return_raw_chat', False),
            truncation=config.data.get('truncation', 'error'),
            filter_overlong_prompts=config.data.filter_overlong_prompts,
            num_workers=config.data.get('filter_overlong_prompts_workers', None),
            is_train=False,
        )

        val_loader = StatefulDataLoader(
            dataset=val_dataset,
            batch_size=config.data.get('batch_size', 32),
            num_workers=config.data.get('dataloader_num_workers', 4),
            shuffle=False,
            drop_last=False,
            collate_fn=collate_fn
        )

        all_outputs = []
        all_ids = []
        all_scores = []

        def do_inference(batch):
            batch_indices = batch['index'].tolist()
            input_items = SampleItemList()
            for i, idx in enumerate(batch_indices):
                item = SampleItem(
                    org_input=batch['input'][i],
                    llm_input=batch['input_ids'][i],  # Will be modified by modify_prompts
                    org_input_id=batch['output'][i]
                )
                input_items.append(item)
            
            # Modify prompts in memory and run inference
            # input_items = self.modify_prompts(input_items)
            shot_number = config.rollout.get('shot_number', 1)
            inputs,outputs = llm_inference.run_inference(
                input_items, 
                shot_number, 
                generation_config=config.rollout
            )
            # print("===="*100)
            # print(f"shot: {shot_number}")
            # print(f"batch indices: {batch_indices}")
            # print(f"outputs: {outputs[0]}")
            # print("===="*100)
            return inputs,outputs
            
        # Process each batch
        for batch in tqdm(val_loader, desc="Processing batches", unit="batch"):
            batch_indices = batch['index'].tolist()
            # print(model_path, " DEBUG: batch_indices", batch_indices)
            ground_truth = batch['output']  # Get ground truth from batch
            
            # Get all shots for each input in the batch
            inputs,batch_outputs_all_shots = do_inference(batch)
            
            batch_all_scores = []
            shot_number = config.rollout.get('shot_number', 1)
            
            # Process each shot
            for shot_idx in range(shot_number):
                shot_scores = []
                # Get outputs for current shot
                llm_outputs = []
                for idx, outputs in enumerate(batch_outputs_all_shots):
                    llm_output = outputs[shot_idx]
                    # print(model_path, f"LLM output: {llm_output}")
                    llm_outputs.append(llm_output)
                        
                # Process the LLM output to get combined sequence
                solution_str_list = prepare_llm_output(inputs, llm_outputs, batch, model.tokenizer)
                
                # Compute score for each solution in the list
                shot_scores = []
                # print(f"\n{bcolors.OKBLUE}=== Debug: Processed Output ==={bcolors.ENDC}")
                
                # Prepare tasks for parallel processing
                tasks = []
                for solution_idx, solution_str in enumerate(solution_str_list):
                    # print(f"DEBUG: solution_str: {solution_str}")
                    task = (
                        solution_str,
                        {'ground_truth': ground_truth[solution_idx]},
                        batch_indices[solution_idx],
                        exp_name,
                        config.reward_model.reward_type,
                        config.trainer.output_dir
                    )

                    _dir = os.path.join(config.trainer.output_dir, str(batch_indices[solution_idx]))
                    os.makedirs(_dir, exist_ok=True)
                    # print("DEBGU: extract_solution")
                    gt_code = ground_truth[solution_idx]   
                    code = extract_solution(solution_str=solution_str)
                    input_code = extract_input(solution_str=solution_str)

                    if not os.path.exists(os.path.join(_dir, "gt.dfy")):
                        fn = os.path.join(_dir, "gt.dfy")
                        f = open(fn, "w")
                        f.write(gt_code)
                        f.close()
                    # print("DEBGU: save gt")

                    if code is None:
                        num_files = len(os.listdir(_dir))
                        number = num_files * 10000 + random.randint(0, 9999)
                        fn = os.path.join(_dir, f"{number}.dfy")
                        f = open(fn, "w")
                        f.write("No codestring found")
                        f.close()
                    elif input_code is None:
                        num_files = len(os.listdir(_dir))
                        number = num_files * 10000 + random.randint(0, 9999)
                        fn = os.path.join(_dir, f"{number}.dfy")
                        f = open(fn, "w")
                        f.write("No input found")
                        f.close()
                        print(f"Solution string: {solution_str}")
                        print("No input found")
                    elif not is_fuzzy_match(input_code, code):
                        num_files = len(os.listdir(_dir))
                        number = num_files * 10000 + random.randint(0, 9999)
                        fn = os.path.join(_dir, f"{number}.dfy")
                        f = open(fn, "w")
                        f.write("original code changed")
                        f.close()
                    else:
                        num_files = len(os.listdir(_dir))
                        number = num_files * 10000 + random.randint(0, 9999)
                        fn = os.path.join(_dir, f"{number}.dfy")

                        f = open(fn, "w")
                        f.write(code)
                        f.close()
                    tasks.append(task)
                    
        #         # Use ProcessPoolExecutor for parallel computation
        #         max_workers = config.data.get('batch_size', min(len(tasks), 12))  # Default to 8 workers or number of tasks
        #         print(f"Using parallel processing with {max_workers} workers for {len(tasks)} tasks")
                
        #         try:
        #             with ProcessPoolExecutor(max_workers=max_workers) as executor:
        #                 # Submit all tasks
        #                 future_to_idx = {executor.submit(compute_score_parallel, task): idx 
        #                                 for idx, task in enumerate(tasks)}
                        
        #                 # Collect results in order
        #                 shot_scores = [None] * len(tasks)
        #                 for future in as_completed(future_to_idx):
        #                     idx = future_to_idx[future]
        #                     try:
        #                         score = future.result()
        #                         shot_scores[idx] = score
        #                     except Exception as exc:
        #                         import traceback
        #                         print(f'Task {idx} generated an exception: {exc}')
        #                         shot_scores[idx] = [0] * 9  # Default score on error
        #         except Exception as e:
        #             print(f"Parallel processing failed: {e}. Falling back to sequential processing.")
        #             use_parallel = False
                
        #         # for idx, (solution, score) in enumerate(zip(solution_str_list, shot_scores)):
        #         #     print(f"Score {idx}: {score}\n") 
                
        #         batch_all_scores.append(shot_scores)
            
        #     # Transpose batch_all_scores to group scores by input rather than by shot
        #     batch_all_scores = list(zip(*batch_all_scores))
            
        #     all_outputs.extend(batch_outputs_all_shots)
        #     all_ids.extend(batch_indices)
        #     all_scores.extend([list(scores) for scores in batch_all_scores])

        # # Save results
        # output_data = save_inference_outputs(
        #     all_outputs, 
        #     all_ids, 
        #     all_scores, 
        #     exp_name, 
        #     save=config.trainer.save_output,
        #     output_dir=config.trainer.output_dir
        # )
        # return output_data

@hydra.main(config_path='config', config_name='generation', version_base=None)
def main(config):
    # Print and lock-down config
    print(f"\n{bcolors.OKBLUE}=== Debug: Config ==={bcolors.ENDC}")
    print(OmegaConf.to_yaml(config))
    
    # Create and run evaluator
    evaluator = EvalRunner()
    evaluator.run(config)
    # output_data = evaluator.run(config)
    # with open(os.path.join(config.trainer.output_dir, "eval_results.json"), "w") as f:
    #     json.dump(output_data, f, indent=2)
    
    # return output_data

if __name__ == "__main__":
    main()