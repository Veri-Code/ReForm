import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
from typing import List, Dict, Tuple
import glob
from pathlib import Path
import subprocess
from verl.inference.eval import main as eval_main
import sys
import hydra
from hydra.core.hydra_config import HydraConfig
from omegaconf import DictConfig, OmegaConf
import yaml
import torch.multiprocessing as mp
import torch
import itertools
import logging


def setup_logging(log_dir, log_filename='plot.log'):
    """Set up logging configuration that works across processes."""
    os.makedirs(log_dir, exist_ok=True)
    
    # Create logger
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    
    # Clear any existing handlers
    for handler in logger.handlers[:]:
        logger.removeHandler(handler)
    
    # Create formatters
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    
    # File handler
    file_handler = logging.FileHandler(os.path.join(log_dir, log_filename), mode='a')
    file_handler.setLevel(logging.INFO)
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)
    
    # Console handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    
    return logger

def log_and_print(message, level='info'):
    """Log message and print to console, with fallback if logger not available."""
    try:
        logger = logging.getLogger()
        if logger.handlers:  # Check if logger is properly configured
            getattr(logger, level)(message)
        else:
            print(f"[{level.upper()}] {message}")
    except:
        print(f"[{level.upper()}] {message}")


def parse_args():
    parser = argparse.ArgumentParser(description='Plot evaluation results for multiple experiments')
    
    # Config file option
    parser.add_argument('--config', type=str, help='Path to config file (yaml or json)')
    
    # Direct arguments that can override config file
    parser.add_argument('--base_path', type=str, default="/oss/public/user/chefengdi/ckpts",
                      help='Base path to model checkpoints')
    parser.add_argument('--exp_names', nargs='+', help='List of experiment names to compare')
    parser.add_argument('--global_steps', nargs='+', type=int, default=[20, 40, 100],
                      help='List of global steps to evaluate')
    parser.add_argument('--shot_numbers', nargs='+', type=int, default=[1, 2, 3],
                      help='List of shot numbers to analyze')
    parser.add_argument('--output_dir', type=str, default="plots/comparison",
                      help='Directory to save output plots')
    
    return parser.parse_args()

def load_config(config_path: str) -> dict:
    """Load configuration from yaml or json file"""
    if config_path.endswith('.yaml') or config_path.endswith('.yml'):
        with open(config_path, 'r') as f:
            return yaml.safe_load(f)
    elif config_path.endswith('.json'):
        with open(config_path, 'r') as f:
            return json.load(f)
    else:
        raise ValueError("Config file must be either yaml or json")

def get_model_path(exp_name: str):
    if '0.5B' in exp_name:
        model_path = "/oss/public/user/xuxu/distilled/ckpt_opt/SKD_RKL-0.5B_14B"
    elif '1.5B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-1.5B_5k_sft_opt"
    elif '3B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt"
    elif '7B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-7B_5k_sft_opt"
    elif '14B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-14B_5k_sft_opt"
    else:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt"
    return model_path

def get_qwen_coder_model_path(exp_name: str):
    if '0.5B' in exp_name:
        model_path = "/cpfs04/user/liyizhi/models/Qwen2.5-Coder-0.5B"
    elif '1.5B' in exp_name:
        model_path = "/cpfs04/user/liyizhi/models/Qwen2.5-Coder-1.5B"
    elif '3B' in exp_name:
        model_path = "/cpfs04/user/liyizhi/models/Qwen2.5-Coder-3B"
    elif '7B' in exp_name:
        model_path = "/cpfs04/user/liyizhi/models/Qwen2.5-Coder-7B"
    elif '14B' in exp_name:
        model_path = "/cpfs04/user/liyizhi/models/Qwen2.5-Coder-14B"
    elif '32B' in exp_name:
        model_path = "/cpfs04/user/liyizhi/models/Qwen2.5-Coder-32B"
    return model_path


def run_single_eval(task_with_gpu):
    """Run evaluation for a single model checkpoint on a specific GPU."""
    task, gpu_ids = task_with_gpu
    model_path = task['model_path']
    max_shot = task['max_shot']
    config = task['config']
    exp_name = task['exp_name']
    step = task['step']
    
    try:
        # Set GPU devices for multi-GPU inference
        if isinstance(gpu_ids, list):
            # Multi-GPU case
            os.environ["CUDA_VISIBLE_DEVICES"] = ",".join(map(str, gpu_ids))
            tensor_parallel_size = len(gpu_ids)
        else:
            # Single GPU case (backward compatibility)
            os.environ["CUDA_VISIBLE_DEVICES"] = str(gpu_ids)
            tensor_parallel_size = 1
        
        # Initialize CUDA device
        torch.cuda.init()
        device = torch.device(f'cuda:0')  # Always use cuda:0 since we set CUDA_VISIBLE_DEVICES
        torch.cuda.set_device(device)
        
        # Create a copy of the config
        config = OmegaConf.create(config)
        
        step_name = os.path.basename(os.path.dirname(model_path))
        
        # Get base log directory and update output directory
        log_dir = config.trainer.get('output_dir', "/nas/shared/sys2/chefengdi/dafny_full_log/")
        cpu_num = config.data.get('cpu_num', 8)
        config.trainer.output_dir = os.path.join(log_dir, f"{exp_name}", f"{step_name}")
        
        # Override specific values
        config.model.path = model_path
        config.rollout.shot_number = max_shot
        config.trainer.n_gpus_per_node = tensor_parallel_size
        
        # Set tensor parallel size for multi-GPU inference
        if 'parallel_processing' not in config:
            config.parallel_processing = {}
        config.parallel_processing.tensor_parallel_size = tensor_parallel_size
        
        # Ensure dataset configurations are properly set
        if 'data' not in config:
            config.data = {}
        
        # Dataset configuration
        config.data.filter_overlong_prompts_workers = 1  # Must be > 0 for dataset filtering
        config.data.dataloader_num_workers = 0  # Disable DataLoader workers
        config.data.batch_size = tensor_parallel_size* int(cpu_num) # Process one sample at a time
        config.data.return_raw_chat = False
        config.data.truncation = 'error'
        
        log_and_print(f"Running evaluation on GPUs {gpu_ids}: {exp_name} - Step {step} (tensor_parallel_size={tensor_parallel_size})")
        results = eval_main(config)
        return task['exp_name'], task['step'], results
    except Exception as e:
        log_and_print(f"Error evaluating {model_path} on GPUs {gpu_ids}: {str(e)}", 'error')
        import traceback
        traceback.print_exc()
        return task['exp_name'], task['step'], None


@hydra.main(version_base=None, config_path="conf", config_name="config")
def main(cfg: DictConfig) -> None:
    """
    Main function to run the analysis and generate plots for multiple experiments.
    """
    print("Running with configuration:")
    print(OmegaConf.to_yaml(cfg))

    # Set up comprehensive logging to both file and console
    log_dir = cfg.trainer.get('output_dir', "./logs")
    os.makedirs(log_dir, exist_ok=True)
    
    # Create logger
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    
    # Clear any existing handlers
    for handler in logger.handlers[:]:
        logger.removeHandler(handler)
    
    # Create formatters
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    
    # File handler
    file_handler = logging.FileHandler(os.path.join(log_dir, 'plot.log'), mode='a')
    file_handler.setLevel(logging.INFO)
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)
    
    # Console handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)
    
    # Capture stderr to logger as well
    class LoggerWriter:
        def __init__(self, logger, level):
            self.logger = logger
            self.level = level
        
        def write(self, message):
            if message.strip():  # Only log non-empty messages
                self.logger.log(self.level, message.strip())
        
        def flush(self):
            pass
    
    # Redirect stderr to logger
    sys.stderr = LoggerWriter(logger, logging.ERROR)
    
    logger.info("Starting evaluation and plotting process")
    logger.info(f"Configuration:\n{OmegaConf.to_yaml(cfg)}")
    
    # Extract plot-specific configuration
    plot_cfg = cfg.get('plot', {})
    exp_names = plot_cfg.get('exp_names', [
        "3B"
    ])
    model_paths = plot_cfg.get('base_paths', [
        "/oss/public/user/chefengdi/ckpts"
    ])
    global_steps =[0]
    shot_numbers = plot_cfg.get('shot_numbers', [8])

    import datetime

    x  = datetime.datetime.now()
    date = [str(x.month),str(x.day),"hour",str(x.hour)]
    date = '-'.join(date)

    plot_dir = os.path.join(log_dir, f"plots_{date}")
    
    # Create logs directory if it doesn't exist
    os.makedirs(log_dir, exist_ok=True)
    os.makedirs(plot_dir, exist_ok=True)
    
    logger.info(f"Log directory: {log_dir}")
    logger.info(f"Plot directory: {plot_dir}")
    logger.info(f"Experiment names: {exp_names}")
    logger.info(f"Global steps: {global_steps}")
    logger.info(f"Shot numbers: {shot_numbers}")
    
    # Get tensor parallel size from config
    tensor_parallel_size = cfg.get('parallel_processing', {}).get('tensor_parallel_size', 1)
    
    # Get available GPUs
    num_gpus = torch.cuda.device_count()
    if num_gpus == 0:
        logger.error("No GPUs available for evaluation")
        raise RuntimeError("No GPUs available for evaluation")
    logger.info(f"Found {num_gpus} GPUs, using tensor_parallel_size={tensor_parallel_size}")
    
    # Validate GPU configuration
    if num_gpus < tensor_parallel_size:
        error_msg = f"Not enough GPUs ({num_gpus}) for tensor_parallel_size ({tensor_parallel_size})"
        logger.error(error_msg)
        raise ValueError(error_msg)
    
    # Get the maximum shot number
    max_shot = max(shot_numbers)
    logger.info(f"Maximum shot number: {max_shot}")
    
    # Create all evaluation tasks
    logger.info("Creating evaluation tasks...")

    exp_names = []
    
    for model_path in model_paths:
        exp_name = model_path.split("/")[-1]
        exp_names.append(exp_name)
        os.makedirs(os.path.join(log_dir, exp_name), exist_ok=True)
        log_dir_sft = os.path.join(log_dir, exp_name)
        cfg.trainer.output_dir = log_dir_sft
        task = {
            'model_path': model_path,
            'step': 0,
            'exp_name': exp_name,
            'max_shot': max_shot,
            'config': cfg
        }
        
        gpu_group = list(range(0, tensor_parallel_size))
        task_with_gpu = (task, gpu_group)
        run_single_eval(task_with_gpu)

if __name__ == "__main__":
    # Set multiprocessing start method to 'spawn'
    mp.set_start_method('spawn', force=True)
    main()
    # run_sft()
