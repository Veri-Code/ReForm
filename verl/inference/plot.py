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
    elif '3B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt"
    elif '7B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-7B_5k_sft_opt"
    elif '14B' in exp_name:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-14B_5k_sft_opt"
    else:
        model_path = "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt"
    return model_path

def create_eval_tasks(base_paths: List[str], exp_names: List[str], global_steps: List[int], max_shot: int, base_config: DictConfig):
    """Create evaluation tasks for all experiments and steps."""
    eval_tasks = []
    for i, (base_path, exp_name) in enumerate(zip(base_paths, exp_names)):
        for step in global_steps:
            model_path = os.path.join(base_path, exp_name, f"global_step_{step}", "actor")
            eval_tasks.append({
                'model_path': model_path,
                'step': step,
                'exp_name': exp_name,
                'max_shot': max_shot,
                'config': base_config
            })
    return eval_tasks

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
        num_cpu = config.data.get('num_cpu', 1)
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
        config.data.batch_size = tensor_parallel_size * int(num_cpu)  # Process one sample at a time
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

def worker_process(task_with_gpu, queue):
    """Worker function for parallel evaluation."""
    try:
        # Set up logging for this worker process
        task, gpu_ids = task_with_gpu
        exp_name = task['exp_name']
        step = task['step']
        
        # Try to set up logging for worker
        try:
            
            # Create a simple logger for this worker
            worker_logger = logging.getLogger(f'worker_{exp_name}_{step}')
            worker_logger.setLevel(logging.INFO)
            
            # Only add handlers if they don't exist
            if not worker_logger.handlers:
                # Console handler for worker
                console_handler = logging.StreamHandler(sys.stdout)
                console_handler.setLevel(logging.INFO)
                formatter = logging.Formatter(f'%(asctime)s - WORKER[{exp_name}_step{step}] - %(levelname)s - %(message)s')
                console_handler.setFormatter(formatter)
                worker_logger.addHandler(console_handler)
            
            worker_logger.info(f"Worker started for {exp_name} step {step} on GPUs {gpu_ids}")
        except Exception as logging_error:
            print(f"Worker logging setup failed: {logging_error}")
        
        # Run the actual evaluation
        result = run_single_eval(task_with_gpu)
        
        if result[2] is not None:  # result[2] is the evaluation results
            try:
                worker_logger.info(f"Worker completed successfully for {exp_name} step {step}")
            except:
                print(f"Worker completed successfully for {exp_name} step {step}")
        
        queue.put(result)
        
    except Exception as e:
        error_msg = f"Worker process error for {task.get('exp_name', 'unknown')} step {task.get('step', 'unknown')}: {str(e)}"
        log_and_print(error_msg, 'error')
        
        # Try to log full traceback
        try:
            import traceback
            traceback_msg = f"Worker traceback: {traceback.format_exc()}"
            log_and_print(traceback_msg, 'error')
            
            # Also print to stderr in case logging fails
            print(error_msg, file=sys.stderr)
            print(traceback_msg, file=sys.stderr)
        except Exception as trace_error:
            print(f"Failed to log traceback: {trace_error}", file=sys.stderr)
        
        queue.put(None)

def run_parallel_eval(tasks_with_gpus, num_gpus, tensor_parallel_size):
    """Run evaluations in parallel using Process with better GPU utilization."""
    results = []
    
    try:
        # Calculate how many tasks can run in parallel based on GPU requirements
        max_parallel_tasks = num_gpus // tensor_parallel_size
        if max_parallel_tasks == 0:
            error_msg = f"Not enough GPUs ({num_gpus}) for tensor_parallel_size ({tensor_parallel_size})"
            log_and_print(error_msg, 'error')
            raise ValueError(error_msg)
        
        log_and_print(f"Running {len(tasks_with_gpus)} tasks with {max_parallel_tasks} parallel processes (tensor_parallel_size={tensor_parallel_size})")
        
        # Use a more efficient approach: start new processes as soon as GPUs become available
        import queue
        import threading
        
        # Create a queue for available GPU groups
        available_gpu_groups = queue.Queue()
        for i in range(max_parallel_tasks):
            start_gpu = i * tensor_parallel_size
            gpu_group = list(range(start_gpu, start_gpu + tensor_parallel_size))
            available_gpu_groups.put(gpu_group)
        
        # Queue for results
        results_queue = mp.Queue()
        
        # Track running processes
        running_processes = {}
        completed_tasks = 0
        total_tasks = len(tasks_with_gpus)
        
        # Start initial batch of processes
        task_iter = iter(tasks_with_gpus)
        
        def start_process_if_available():
            """Start a new process if GPU group is available and tasks remain."""
            # try:
            if not available_gpu_groups.empty():
                gpu_group = available_gpu_groups.get_nowait()
                task = next(task_iter)  # Ignore the original GPU assignment
                task_with_gpu = (task, gpu_group)
                
                p = mp.Process(
                    target=worker_process,
                    args=(task_with_gpu, results_queue)
                )
                p.start()
                running_processes[p.pid] = (p, gpu_group)
                log_and_print(f"Started task on GPUs {gpu_group}: {task['exp_name']} - Step {task['step']}")
                return True
            # except queue.Empty:
            #     log_and_print("No available GPU groups", 'debug')
            #     pass
            # except StopIteration:
            #     log_and_print("No more tasks to process", 'debug')
            #     pass
            # except Exception as e:
            #     log_and_print(f"Error starting process: {str(e)}", 'error')
            #     import traceback
            #     log_and_print(f"Traceback: {traceback.format_exc()}", 'error')
            # return False
        
        # Start initial processes
        log_and_print("Starting initial batch of processes...")
        initial_started = 0
        while len(running_processes) < max_parallel_tasks and start_process_if_available():
            initial_started += 1
        log_and_print(f"Started {initial_started} initial processes")
        
        # Monitor and restart processes as they complete
        log_and_print("Monitoring process completion...")
        while completed_tasks < total_tasks:
            try:
                # Check for completed processes
                completed_in_iteration = 0
                for pid, (process, gpu_group) in list(running_processes.items()):
                    try:
                        if not process.is_alive():
                            exit_code = process.exitcode
                            process.join(timeout=5)  # Add timeout to prevent hanging
                            
                            if exit_code != 0:
                                log_and_print(f"Process {pid} exited with code {exit_code}", 'warning')
                            
                            available_gpu_groups.put(gpu_group)  # Return GPU group to available pool
                            del running_processes[pid]
                            completed_tasks += 1
                            completed_in_iteration += 1
                            
                            # Try to start a new process
                            if start_process_if_available():
                                log_and_print(f"Started replacement process after completion", 'debug')
                    except Exception as e:
                        log_and_print(f"Error checking process {pid}: {str(e)}", 'error')
                        # Force cleanup of problematic process
                        try:
                            if process.is_alive():
                                process.terminate()
                                process.join(timeout=5)
                            available_gpu_groups.put(gpu_group)
                            del running_processes[pid]
                            completed_tasks += 1
                        except Exception as cleanup_error:
                            log_and_print(f"Error during process cleanup: {str(cleanup_error)}", 'error')
                
                if completed_in_iteration > 0:
                    log_and_print(f"Completed {completed_in_iteration} tasks. Progress: {completed_tasks}/{total_tasks}")
                
                # Collect results
                results_collected = 0
                try:
                    while not results_queue.empty():
                        result = results_queue.get_nowait()
                        if result is not None:
                            results.append(result)
                            results_collected += 1
                        else:
                            log_and_print("Received None result from worker", 'warning')
                except queue.Empty:
                    pass
                except Exception as e:
                    log_and_print(f"Error collecting results: {str(e)}", 'error')
                
                if results_collected > 0:
                    log_and_print(f"Collected {results_collected} results. Total results: {len(results)}")
                
                # Small sleep to prevent busy waiting
                import time
                time.sleep(0.1)
                
            except Exception as e:
                log_and_print(f"Error in main monitoring loop: {str(e)}", 'error')
                import traceback
                log_and_print(f"Traceback: {traceback.format_exc()}", 'error')
                # Continue the loop to try to recover
                continue
        
        # Wait for any remaining processes
        log_and_print("Waiting for remaining processes to complete...")
        remaining_processes = list(running_processes.items())
        for pid, (process, gpu_group) in remaining_processes:
            try:
                if process.is_alive():
                    log_and_print(f"Waiting for process {pid} to complete...")
                    process.join(timeout=30)  # Add timeout
                    if process.is_alive():
                        log_and_print(f"Process {pid} did not complete within timeout, terminating...", 'warning')
                        process.terminate()
                        process.join(timeout=5)
            except Exception as e:
                log_and_print(f"Error waiting for process {pid}: {str(e)}", 'error')
        
        # Collect any remaining results
        log_and_print("Collecting any remaining results...")
        final_results_collected = 0
        try:
            while not results_queue.empty():
                result = results_queue.get_nowait()
                if result is not None:
                    results.append(result)
                    final_results_collected += 1
        except Exception as e:
            log_and_print(f"Error collecting final results: {str(e)}", 'error')
        
        log_and_print(f"Collected {final_results_collected} final results. Total results: {len(results)}")
        log_and_print(f"Parallel evaluation completed. Total results: {len(results)}, Expected tasks: {total_tasks}")
        
        return results
        
    except Exception as e:
        log_and_print(f"Critical error in run_parallel_eval: {str(e)}", 'error')
        import traceback
        log_and_print(f"Full traceback: {traceback.format_exc()}", 'error')
        
        # Attempt cleanup
        try:
            log_and_print("Attempting cleanup of any remaining processes...", 'warning')
            if 'running_processes' in locals():
                for pid, (process, gpu_group) in running_processes.items():
                    try:
                        if process.is_alive():
                            process.terminate()
                            process.join(timeout=5)
                    except Exception as cleanup_error:
                        log_and_print(f"Error during emergency cleanup of process {pid}: {str(cleanup_error)}", 'error')
        except Exception as final_cleanup_error:
            log_and_print(f"Error during final cleanup: {str(final_cleanup_error)}", 'error')
        
        # Return any results we managed to collect
        if 'results' in locals():
            log_and_print(f"Returning {len(results)} results despite error", 'warning')
            return results
        else:
            log_and_print("No results to return due to critical error", 'error')
            return []

def compute_cumulative_binary_scores(results: Dict, global_steps: List[int], shot_numbers: List[int]) -> Dict:
    """
    Process scores for each step and shot, aggregating across shots using OR or mean operations.
    
    Args:
        results: Dictionary containing scores for each step and shot
        global_steps: List of global steps
        shot_numbers: List of shot numbers in ascending order (all valid shots)
    
    Returns:
        Dictionary containing aggregated scores for each step
    """
    cumulative_results = {}
    
    # Indices that use mean operation - updated for 9 scores
    # Define which scores are binary (OR) vs continuous (mean)
    or_indices = [0, 1, 2, 8]  # Binary metrics
    mean_indices = [6]  # Continuous metrics
    min_indices = [3, 4, 5, 7]

    for step in global_steps:
        cumulative_results[step] = {}

        # Stack all shots' scores for this step
        all_shot_scores = []
        for shot in range(1, max(shot_numbers) + 1):
            if shot in results[step] and len(results[step][shot]) > 0:
                all_shot_scores.append(results[step][shot])

            stacked_scores = np.stack(all_shot_scores, axis=1)  # Shape: (N, num_shots, 9)
            
            # Initialize aggregated scores array - updated to 9 scores
            aggregated_scores = np.zeros((stacked_scores.shape[0], 9))
            
            # Apply OR operation for binary metrics
            for idx in or_indices:
                aggregated_scores[:, idx] = np.max(stacked_scores[:, :, idx], axis=1)
            
            # Apply mean operation for continuous metrics
            for idx in mean_indices:
                aggregated_scores[:, idx] = np.mean(stacked_scores[:, :, idx], axis=1)

            for idx in min_indices:
                aggregated_scores[:, idx] = np.min(stacked_scores[:, :, idx], axis=1)
                
            # Store the aggregated scores for each shot
            cumulative_results[step][shot] = aggregated_scores
    
    return cumulative_results

def plot_scores(exp_results: Dict[str, Dict], global_steps: List[int], shot_numbers: List[int], 
                output_dir: str):
    """Plot scores for each experiment across different global steps."""
    # Create consistent color mapping for experiments
    exp_names = list(exp_results.keys())
    colors = sns.color_palette("husl", len(exp_names))
    color_map = {exp_names[i]: colors[i] for i in range(len(exp_names))}
    
    # Define which scores to plot and their labels
    score_names = [
        "No Parse Error",
        "Verifiable",
        "Strength Score",
        "No Added Assume",
        "No Only Ensures True",
        "No Only Ensures A==A",
        "Number of Intermediate Clauses",
        "No Comments",
        "Novel Spec Score"
    ]
    # Define which scores are binary (OR) vs continuous (mean)
    or_indices = [0, 1, 2, 8]  # Binary metrics
    mean_indices = [6]  # Continuous metrics
    min_indices = [3, 4, 5, 7]
    

    # Create plots for each shot number
    for shot in range(1, max(shot_numbers) + 1):
        # Create a subplot for each score component (5x3 grid for 14 scores, with 1 empty subplot)
        fig, axes = plt.subplots(3, 3, figsize=(24, 40))
        fig.suptitle(f'Cumulative Metrics Comparison for {shot}-shot', fontsize=16)
        axes = axes.flatten()
        
        # Plot each score component
        for i, score_name in enumerate(score_names):
            ax = axes[i]
            
            # Plot each experiment using consistent colors
            for exp_name, exp_data in exp_results.items():
                global_steps = sorted(list(exp_data['cumulative_results'].keys()))
                print("global_steps: ", global_steps)
                cumulative_results = exp_data['cumulative_results']
                
                # Extract means and stds for this score component
                step_means = []
                for step in global_steps:
                    shot_keys = list(cumulative_results[step].keys())
                    shot_keys = [int(shot_key) for shot_key in shot_keys]
                    if shot in shot_keys:
                        # scores = cumulative_results[step][str(shot)]
                        scores = cumulative_results[step][shot]
                        scores = np.array(scores)
                        scores = np.where(scores == -1, 0, scores)
                        mean_score = np.mean(scores[:, i])
                        step_means.append(mean_score)
                
                # Plot line using consistent color
                ax.plot(global_steps, step_means, '-o', label=exp_name, 
                       color=color_map[exp_name])
                
            
            ax.set_xlabel('Global Steps')
            ax.set_ylabel(score_name)
            if i in or_indices:  # OR operation indices - updated for 14th score
                ax.set_title(f'{score_name}\n(OR operation across shots)')
            elif i in min_indices:
                ax.set_title(f'{score_name}\n(Min across shots)')
            else:
                ax.set_title(f'{score_name}\n(Mean across shots)')
            ax.grid(True, alpha=0.3)
            ax.legend()
            
        
        # # Hide the last subplot since we have 14 scores in a 5x3 grid (15 subplots)
        # axes[14].set_visible(False)
        
        # Adjust layout and save
        plt.tight_layout(rect=[0, 0.03, 1, 0.95])
        plt.savefig(os.path.join(output_dir, f'comparison_shot_{shot}.png'), 
                    dpi=300, bbox_inches='tight')
        plt.close()

def plot_scores_vs_shots(exp_results: Dict[str, Dict], global_steps: List[int], shot_numbers: List[int], 
                      output_dir: str, target_steps: List[int] = None):
    """
    Plot scores vs shot numbers for each metric and experiment.
    For each experiment, creates a plot with different lines for each target step.
    
    Args:
        exp_results: Dictionary mapping experiment names to their results dictionaries
                    Format: {exp_name: {'cumulative_results': cumulative_results_dict}}
        global_steps: List of global steps
        shot_numbers: List of shot numbers
        output_dir: Directory to save plots
        target_steps: List of steps to plot (default: [20, 40, 100])
    """
    if target_steps is None:
        target_steps = [20, 40, 60, 80]
    
    # Validate target steps
    valid_target_steps = [step for step in target_steps if step in global_steps]
    if len(valid_target_steps) != len(target_steps):
        print(f"Warning: Some target steps not found in global_steps. Using {valid_target_steps}")
        target_steps = valid_target_steps
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Create consistent color mapping for target steps
    colors = sns.color_palette("husl", len(target_steps))
    step_color_map = {target_steps[i]: colors[i] for i in range(len(target_steps))}
    
    # Score names and their descriptions - updated for 14 scores
    score_names = [
        "No Parse Error",
        "Verifiable",
        "Strength Score",
        "No Added Assume",
        "No Only Ensures True",
        "No Only Ensures A==A",
        "Number of Intermediate Clauses",
        "No Comments",
        "Novel Spec Score"
    ]
    # Define which scores are binary (OR) vs continuous (mean)
    or_indices = [0, 1, 2, 8]  # Binary metrics
    mean_indices = [6]  # Continuous metrics
    min_indices = [3, 4, 5, 7]
    
    # Create plots for each experiment
    for exp_name, exp_data in exp_results.items():
        cumulative_results = exp_data['cumulative_results']
        
        # Create a 3x3 subplot grid for all 9 scores
        fig, axes = plt.subplots(3, 3, figsize=(24, 40))
        fig.suptitle(f'Score vs Number of Shots for {exp_name}', fontsize=16)
        axes = axes.flatten()
        
        # Plot each score component
        for i, score_name in enumerate(score_names):
            ax = axes[i]
            
            # Plot each target step using consistent colors
            for target_step in target_steps:
                # Extract means and stds for this score component across shots
                shot_means = []
                shot_stds = []
                
                for shot in range(1, max(shot_numbers) + 1):
                    shot_keys = list(cumulative_results[target_step].keys())
                    shot_keys = [int(shot_key) for shot_key in shot_keys]
                    if shot in shot_keys:
                        # scores = cumulative_results[target_step][str(shot)]
                        scores = cumulative_results[target_step][shot]
                        scores = np.array(scores)
                        scores = np.where(scores == -1, 0, scores)
                        mean_score = np.mean(scores[:, i])
                        shot_means.append(mean_score)
                    else:
                        shot_means.append(np.nan)
                        shot_stds.append(0)
                
                # Plot line for this step using consistent color
                ax.plot(range(1, max(shot_numbers) + 1), shot_means, '-o', 
                       label=f'Step {target_step}', 
                       color=step_color_map[target_step])
                
                # # Only show error bands for mean-based metrics
                # if i in mean_indices:
                #     ax.fill_between(shot_numbers, 
                #                   np.array(shot_means) - np.array(shot_stds),
                #                   np.array(shot_means) + np.array(shot_stds),
                #                   alpha=0.2, color=step_color_map[target_step])
            
            ax.set_xlabel('Number of Shots')
            ax.set_ylabel(score_name)
            if i in or_indices:  # OR operation indices - updated for 14th score
                ax.set_title(f'{score_name}\n(OR operation)')
            elif i in min_indices:
                ax.set_title(f'{score_name}\n(Min operation)')
            else:
                ax.set_title(f'{score_name}\n(Mean operation)')
            ax.grid(True, alpha=0.3)
            ax.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
            
        
        # # Hide the last subplot since we have 14 scores in a 5x3 grid (15 subplots)
        # axes[14].set_visible(False)
        
        # Adjust layout and save
        plt.tight_layout(rect=[0, 0.03, 1, 0.95])
        plt.savefig(os.path.join(output_dir, f'shots_comparison_{exp_name}.png'), 
                    dpi=300, bbox_inches='tight')
        plt.close()

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
    base_paths = plot_cfg.get('base_paths', ["/oss/public/user/chefengdi/ckpts"])
    exp_names = plot_cfg.get('exp_names', [
        "grpo_8nodes_5ksft_3B_spec_refine_one_score-ensures_fixed"
    ])
    global_steps = plot_cfg.get('global_steps', [20, 40, 60, 80])
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
    eval_tasks = []
    
    # if not os.path.exists(os.path.join(log_dir, "sft_ckpt")):
    #     eval_tasks.append({
    #             'model_path': get_model_path(exp_names[0]),
    #             'step': 0,
    #             'exp_name': 'sft_ckpt',
    #             'max_shot': max_shot,
    #             'config': cfg
    #         })
    eval_tasks = eval_tasks + create_eval_tasks(base_paths, exp_names, global_steps, max_shot, cfg)
    logger.info(f"Created {len(eval_tasks)} evaluation tasks")
    
    # Initialize results dictionary for all experiments
    results_dict = {exp_name: {step: {} for step in global_steps + [0]} for exp_name in exp_names}
    results_dict['sft_ckpt'] = {0: {}}
    for exp_name in exp_names:
        for step in global_steps:
            for shot in range(1, max_shot + 1):
                results_dict[exp_name][step][shot] = []
    
    # Initialize SFT checkpoint results
    for shot in range(1, max_shot + 1):
        results_dict['sft_ckpt'][0][shot] = []

    # Run evaluations in parallel
    logger.info("Starting parallel evaluation...")
    eval_results = run_parallel_eval(eval_tasks, num_gpus, tensor_parallel_size)
    logger.info(f"Completed parallel evaluation. Got {len(eval_results)} results.")
    
    # Process results
    logger.info("Processing evaluation results...")
    exp_results = {}
    for exp_name in exp_names:
        exp_results[exp_name] = {'cumulative_results': {}}
    
    processed_count = 0
    for exp_name, step, step_results in eval_results:
        if step_results is not None:
            # Process each sample's results
            for sample_id, sample_data in step_results.items():
                if isinstance(sample_id, str) and sample_id.isdigit():
                    for shot_data in sample_data["shots"]:
                        shot_num = shot_data["shot_number"]
                        if shot_num <= max_shot:
                            if len(shot_data["score"]) != 9 and sum(shot_data["score"]) == 0:
                                shot_data["score"] =[0,]*9
                            results_dict[exp_name][step][shot_num].append(shot_data["score"])
                            processed_count += 1
        else:
            logger.warning(f"No results for {exp_name} step {step}")
    
    # Copy SFT checkpoint results to step 0 for each experiment
    for exp_name in exp_names:
        for shot in range(1, max_shot + 1):
            results_dict[exp_name][0][shot] = results_dict['sft_ckpt'][0][shot].copy()
    
    logger.info(f"Processed {processed_count} individual results")
    
    # Convert lists to numpy arrays and compute cumulative results
    logger.info("Converting results to numpy arrays and computing cumulative results...")
    for exp_name in exp_names:
        for step in global_steps + [0]:
            for shot in range(1, max_shot + 1):
                scores = results_dict[exp_name][step][shot]
                if scores:
                    results_dict[exp_name][step][shot] = np.array(scores)
                    logger.debug(f"{exp_name} step {step} shot {shot}: {len(scores)} scores")
                else:
                    results_dict[exp_name][step][shot] = np.zeros((1, 9))
                    logger.warning(f"{exp_name} step {step} shot {shot}: No scores, using zeros")
        
        # Compute cumulative results
        logger.info(f"Computing cumulative results for {exp_name}...")
        exp_results[exp_name]['cumulative_results'] = compute_cumulative_binary_scores(
            results_dict[exp_name], global_steps + [0], shot_numbers
        )
    
    # Generate plots and save results
    logger.info("Generating plots...")
    plot_scores(exp_results, global_steps + [0], shot_numbers, plot_dir)
    logger.info(f"Saved main plots to {plot_dir}")
    
    shots_output_dir = os.path.join(log_dir, f"shots_comparison_{date}")
    plot_scores_vs_shots(exp_results, global_steps + [0], shot_numbers, shots_output_dir,target_steps=[0,20,40,60,80])
    logger.info(f"Saved shots comparison plots to {shots_output_dir}")
    
    # Save processed data
    logger.info("Saving processed data...")
    processed_data = {
        'exp_results': exp_results,
        'global_steps': global_steps,
        'shot_numbers': shot_numbers
    }
    processed_data_path = os.path.join(plot_dir, exp_names[0], f'processed_data_{date}.npy')
    os.makedirs(os.path.dirname(processed_data_path), exist_ok=True)
    np.save(processed_data_path, processed_data)
    logger.info(f"Saved processed data to {processed_data_path}")
    
    logger.info("Evaluation and plotting process completed successfully!")

if __name__ == "__main__":
    # Set multiprocessing start method to 'spawn'
    mp.set_start_method('spawn', force=True)
    main()
