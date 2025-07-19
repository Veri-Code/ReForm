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
import pandas as pd

from verl import DataProto
from verl.utils.dataset.rl_dataset import RLHFDataset, collate_fn
from torchdata.stateful_dataloader import StatefulDataLoader
from verl.inference.reward_score.inference_reward import compute_subset_score
from verl.inference.model_utils.models import QwenModel
from verl.inference.model_utils.llm_inference import LLMInference
from verl.inference.model_utils.SampleItems import SampleItem, SampleItemList

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
        
        
        def _modify_row(row):
            """Modify a single row's prompt."""
            import ast
            import numpy as np
            import json
            
            # Try to parse the prompt based on its type
            input_content = row['input']
            prompt = row['prompt']
            
            # Handle numpy array
            if isinstance(prompt, np.ndarray):
                # Convert numpy array to list if it contains objects
                prompt = prompt.tolist()
                
            # Apply the prompt transformation
            modified_prompt = self.prompt_func(input_content)
            
            # Update the prompt format to match expected structure
            if isinstance(prompt, list):
                prompt[0]['content'] = modified_prompt
                # Convert to JSON string for parquet compatibility
                row['prompt'] = json.dumps(prompt)
            else:
                row['prompt'] = modified_prompt
            return row

        # Process parquet file and run inference
        input_file = "/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/test.parquet"

        output_file = os.path.join('/nas/shared/sys2/chefengdi/dafny_full_log/', "sft_test.parquet")

        # Generate output file path if not provided
        if output_file is None:
            basename = os.path.basename(input_file)
            if output_dir:
                output_file = os.path.join(output_dir, f"{self.prompt_type}_{basename}")
            else:
                dirname = os.path.dirname(input_file)
                output_file = os.path.join(dirname, f"{self.prompt_type}_{basename}")
        
        # Copy to local if needed
        local_input = input_file
        
        # Load and modify the parquet file
        df = pd.read_parquet(local_input)
        print("Modifying prompts...")
        modified_df = df.loc[:20]
        
        # Save modified file
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        print(f"Saving modified parquet file to {output_file}")
        
        modified_df.to_parquet(output_file, index=False)
        print("Done!")


@hydra.main(config_path='config', config_name='generation', version_base=None)
def main(config):
    # Print and lock-down config
    print(f"\n{bcolors.OKBLUE}=== Debug: Config ==={bcolors.ENDC}")
    print(OmegaConf.to_yaml(config))
    
    # Create and run evaluator
    evaluator = EvalRunner()
    output_data = evaluator.run(config)
    
    return output_data

if __name__ == "__main__":
    main()