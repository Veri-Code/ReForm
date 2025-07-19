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
import logging, json,shutil
from verl.inference.plot import plot_scores, plot_scores_vs_shots, compute_cumulative_binary_scores
from concurrent.futures import ProcessPoolExecutor, as_completed
from verl.inference.reward_score.inference_reward import compute_subset_score
from verl.inference.log_dir import shot_files
from verl.utils.reward_score.condition_comparison_fixed import *

import matplotlib.pyplot as plt
import numpy as np

deepmind_colors = [
    "#1A1A1A",  
    "#D55E00", #orange verification
    "#CC79A7",  # pink subset
    "#009E73",  # green entropy
    "#0072B2",  # blue SFT
    "#56B4E9",  # light blue 
    "#F0E442",  # yellow
]
markers = ['o', 's', '^', 'v', 'D', 'p', '*', 'x', '+', 'h']

# 单图
# model_sizes = ['0.5B', '1.5B', '3B', '7B', '14B']
# x = np.arange(len(model_sizes))

# curve1 = [59, 70, 75, 79, 81]
# curve2 = [40, 48, 58, 66, 73]
# curve3 = [30, 37, 50, 62, 69]

# plt.figure(figsize=(8, 5))
# plt.plot(x, curve1, label='Naive Reward', marker=markers[1], color=deepmind_colors[1])
# plt.plot(x, curve2, label='Subset Reward', marker=markers[2], color=deepmind_colors[2])
# plt.plot(x, curve3, label='Subset Reward with KL and entropy', marker=markers[3], color=deepmind_colors[3])

# plt.xticks(x, model_sizes)
# plt.xlabel("Model Size")
# plt.ylabel("Verification Rate (%)")
# plt.title("Verification Rate vs. Model Size")

# plt.grid(True, linestyle='--', alpha=0.3)
# plt.legend(loc="lower right")
# plt.tight_layout()
# plt.savefig("test.png")


# # 多图
# model_sizes = ['1.5B', '3B', '7B']
# ckpt_steps = [40, 80, 120]
# rollouts = [1, 2, 4, 8, 16, 32]

# np.random.seed(0)
# data = {
#     size: {
#         step: np.clip(np.linspace(0.5, 0.9, len(rollouts)) + 0.02 * np.random.randn(len(rollouts)), 0, 1)
#         for step in ckpt_steps
#     }
#     for size in model_sizes
# }

# fig, axes = plt.subplots(1, len(model_sizes), figsize=(4 * len(model_sizes), 4), sharey=True)

# for idx, size in enumerate(model_sizes):
#     ax = axes[idx]
#     for i, step in enumerate(ckpt_steps):
#         acc = data[size][step]
#         ax.plot(rollouts, acc, label=f"Step {step}", marker=markers[i+1], color=deepmind_colors[i+1], ms=3)
    
#     ax.set_title(f"Model Size: {size}")
#     ax.set_xlabel("Rollout Number")
#     if idx == 0:
#         ax.set_ylabel("Verification Rate")
#     ax.grid(True, linestyle="--", alpha=0.3)
#     ax.set_xticks(rollouts)
#     ax.legend(loc="lower right")

# fig.suptitle("Verification Rate vs. Rollout Number across Model Sizes", fontsize=14)
# plt.tight_layout(rect=[0, 0, 1, 0.9])
# plt.savefig("test.png")


def compute_score_parallel(input_tuple):
    """Helper function for parallel score computation."""
    solution_str, ground_truth, index, exp_name, version, output_dir = input_tuple
    # print(solution_str)
    # assert solution_str != None
    return compute_subset_score(
        solution_str=solution_str,
        ground_truth=ground_truth,
        index=index,
        exp_name=exp_name,
        version=version,
        output_dir=output_dir,
        eval_plot=True,
        inference=False,
    )

def qwen_coder():
    
    mp.set_start_method('spawn', force=True)
    for size in ['7B']:
        tasks = []
        file_dir = f"/nas/shared/sys2/chefengdi/report_shots/qwen_coder/Qwen2.5-Coder-{size}/Qwen2.5-Coder-{size}/models"
        for index in range(512):
            filelists = [int(x[:-4]) for x in os.listdir(os.path.join(file_dir,str(index))) if x.endswith(".dfy") and x not in ["gt.dfy", "input.dfy"]]
        
            file1 = min(filelists)
            file2 = max(filelists)
            file = os.path.join(file_dir, str(index), f"{file1}.dfy")
            with open(file, "r", encoding="utf-8") as f:
                data = f.read()
            file_gt = os.path.join(file_dir, str(index), "gt.dfy")
            with open(file_gt, "r", encoding="utf-8") as f:
                data2 = f.read()

            task = (
                data,
                data2,
                index,
                f"Qwen-coder-{size}",
                "one_score",
                f"/nas/shared/sys2/chefengdi/eval_log/qwen_eval_{size}"
            )
            tasks.append(task)
        
        print(f"Created {len(tasks)} tasks")
        
        max_workers = 96
        print(f"Starting parallel processing with {max_workers} workers")
        
        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            # Submit all tasks
            print("Submitting tasks to executor...")
            future_to_idx = {executor.submit(compute_score_parallel, task): idx 
                            for idx, task in enumerate(tasks)}
            
            print(f"Submitted {len(future_to_idx)} tasks")
            
            # Collect results in order
            shot_scores = [None] * len(tasks)
            completed_tasks = 0
            
            for future in as_completed(future_to_idx):
                idx = future_to_idx[future]
                try:
                    score = future.result()
                    shot_scores[idx] = score
                    completed_tasks += 1
                    if completed_tasks % 10 == 0:  # Print progress every 10 tasks
                        print(f"Completed {completed_tasks}/{len(tasks)} tasks")
                except Exception as exc:
                    import traceback
                    print(f'Task {idx} generated an exception: {exc}')
                    print(f'Traceback: {traceback.format_exc()}')
                    shot_scores[idx] = [0] * 9  # Default score on error
                    completed_tasks += 1

        scores = np.array(shot_scores)
        print("model size: ", size)
        print(f"Final scores shape: {scores.shape}")
        print(f"Mean scores: {np.mean(scores, axis=0)}")

def gt_novel_spec_rate():
    folder = "/nas/shared/sys2/chefengdi/report_shots/3B_BoN4_subset/global_step_20"
    tasks = []
    for index in range(512):
        file = os.path.join(folder, str(index), "gt.dfy")
        with open(file, "r", encoding="utf-8") as f:
            data = f.read()

        task = (
            data,
            data,
            index,
            "gt_spec",
            "one_score",
            f"/nas/shared/sys2/chefengdi/eval_log/GPT_eval_2"
        )
        tasks.append(task)
    
    print(f"Created {len(tasks)} tasks")
    
    max_workers = 96
    print(f"Starting parallel processing with {max_workers} workers")
    
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        # Submit all tasks
        print("Submitting tasks to executor...")
        future_to_idx = {executor.submit(compute_score_parallel, task): idx 
                        for idx, task in enumerate(tasks)}
        
        print(f"Submitted {len(future_to_idx)} tasks")
        
        # Collect results in order
        shot_scores = [None] * len(tasks)
        completed_tasks = 0
        
        for future in as_completed(future_to_idx):
            idx = future_to_idx[future]
            try:
                score = future.result()
                shot_scores[idx] = score
                completed_tasks += 1
                if completed_tasks % 10 == 0:  # Print progress every 10 tasks
                    print(f"Completed {completed_tasks}/{len(tasks)} tasks")
            except Exception as exc:
                import traceback
                print(f'Task {idx} generated an exception: {exc}')
                print(f'Traceback: {traceback.format_exc()}')
                shot_scores[idx] = [0] * 9  # Default score on error
                completed_tasks += 1

    scores = np.array(shot_scores)
    print("model size: ", size)
    print(f"Final scores shape: {scores.shape}")
    print(f"Mean scores: {np.mean(scores, axis=0)}")
        

def check_GPT():
    # Set multiprocessing start method to 'spawn' before any parallel processing
    mp.set_start_method('spawn', force=True)
    score_lists = {}
    
    file_lists =[
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/generation_res/eval_test_gpt-4o_results_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/generation_res/Qwen2.5-Coder-14B_eval_test_14B_sft-mid_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/generation_res/Qwen2.5-Coder-14B_eval_test_14B-EntropyRL-mid_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/generation_res/dafny100_gpt-4o_results_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/generation_res/Qwen2.5-Coder-14B_dafny100_14B_sft-mid_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/generation_res/Qwen2.5-Coder-14B_dafny100_14B-EntroRL_mid_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/autospec_res/dfyautospec_chain300_gpt-4o_results_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/autospec_res/Qwen2.5-Coder-14B_chain300_partial_SFT-mid_rv.json",
        "/nas/shared/sys2/liyizhi/InferenceTimeScaling4Dafny_yizhi/analysis_results/autospec_res/Qwen2.5-Coder-14B_chain300_partial_RLEntropy-mid_rv.json",
    ]
    for file in file_lists:
        data = []
        print(file)
        with open(file, "r", encoding="utf-8") as f:
            data = json.load(f)
            # f.seek(0)
            # for line in f:
            #     line = line.strip()
            #     if not line:
            #         continue
            #     try:
            #         obj = json.loads(line)
            #         data.append(obj)
            #     except:
            #         print(line)
        
        print(f"Loaded {len(data)} items from file")
        
        tasks = []
        for i,item in enumerate(data):
            code = item['dafny_input']
            gt = item['gt_output']
            id = int(item['self_id'])
            if id%10000 !=0:
                continue
            task = (
                code,
                gt,
                i,
                "GPT-4o",
                "one_score",
                "/nas/shared/sys2/chefengdi/eval_log/GPT_eval_2"
            )
            tasks.append(task)
        
        print(f"Created {len(tasks)} tasks")
        
        max_workers = 96
        print(f"Starting parallel processing with {max_workers} workers")
        
        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            # Submit all tasks
            print("Submitting tasks to executor...")
            future_to_idx = {executor.submit(compute_score_parallel, task): idx 
                            for idx, task in enumerate(tasks)}
            
            print(f"Submitted {len(future_to_idx)} tasks")
            
            # Collect results in order
            shot_scores = [None] * len(tasks)
            completed_tasks = 0
            
            for future in as_completed(future_to_idx):
                idx = future_to_idx[future]
                try:
                    score = future.result()
                    shot_scores[idx] = score
                    completed_tasks += 1
                    if completed_tasks % 10 == 0:  # Print progress every 10 tasks
                        print(f"Completed {completed_tasks}/{len(tasks)} tasks")
                except Exception as exc:
                    import traceback
                    print(f'Task {idx} generated an exception: {exc}')
                    print(f'Traceback: {traceback.format_exc()}')
                    shot_scores[idx] = [0] * 9  # Default score on error
                    completed_tasks += 1

        scores = np.array(shot_scores)
        score_lists[file] = np.mean(scores, axis=0)
        print(f"model: {file}")
        print(f"Final scores shape: {scores.shape}")
        print(f"Mean scores: {np.mean(scores, axis=0)}")
    print(score_lists)


def extract_shots_scores(cumulative_results,score_idx):
    or_indices = [0, 1, 2, 8]  # Binary metrics
    mean_indices = [6]  # Continuous metrics
    min_indices = [3, 4, 5, 7]
    
    # Extract means and stds for this score component across shots
    shot_means = []
    
    for shot in cumulative_results.keys():
        # scores = cumulative_results[target_step][str(shot)]
        scores = cumulative_results[shot]
        scores = np.array(scores)
        scores = np.where(scores == -1, 0, scores)
        mean_score = np.mean(scores[:, score_idx])
        shot_means.append(mean_score)
        
    return shot_means

def clean_data(exp_name,data,max_shot=128,global_steps=['2']):
    results_dict = {exp_name: {step: {} for step in global_steps }}
    exp_results = {}
    exp_results[exp_name] = {}
    exp_results[exp_name]['cumulative_results'] ={}
    for step in global_steps:
        for shot in range(1, max_shot + 1):
            results_dict[exp_name][step][shot] = []
    for sample_id, sample_data in data.items():
            if isinstance(sample_id, str) and sample_id.isdigit():
                for shot_data in sample_data["shots"]:
                    shot_num = shot_data["shot_number"]
                    if shot_num <= max_shot:
                        if len(shot_data["score"]) != 9 :
                            shot_data["score"] =[0,]*9
                        results_dict[exp_name][step][shot_num].append(shot_data["score"])
    for step in global_steps:
        for shot in range(1, max_shot + 1):
            scores = results_dict[exp_name][step][shot]
            if scores:
                results_dict[exp_name][step][shot] = np.array(scores)
            else:
                results_dict[exp_name][step][shot] = np.zeros((1, 9))
    
    # Compute cumulative results
    exp_results[exp_name]['cumulative_results'] = compute_cumulative_binary_scores(
        results_dict[exp_name], global_steps, range(1, max_shot + 1)
    )
    return exp_results[exp_name]

def clean_data_2(data,max_shot=128,global_steps=['2']):
    new_data = {}
    new_data= {}
    new_data['2'] = {}
    exp_results = {}
    exp_results['cumulative_results'] = {}
    for i, step in enumerate(data['cumulative_results'].keys()):
        new_data['2'][i+1] = data['cumulative_results'][step]['1']
    
    # Compute cumulative results
    exp_results['cumulative_results'] = compute_cumulative_binary_scores(
        new_data, global_steps, range(1, max_shot + 1)
    )

    return exp_results

def plot_novel_spec():

    wrong_data=[
         "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset/scores_7-11-hour-11/global_step_40_scores_7-11-hour-11.json",
        "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score/scores_7-10-hour-22/saves_scores_7-10-hour-22.json"
        ]

    score_idx = 8
    model_names = [
        # "naive",
        "subset",
        "entropy"
    ]

    rollouts = [1, 32,64,96,128]
    plt.figure(figsize=(8, 5))
    for file in shot_files['sft']:
        with open(file, 'r') as f:
            data = json.load(f)
        if file.endswith("eval_results.json"):
            data = clean_data(model,data)
        elif file in wrong_data:
            data = clean_data_2(data)
        # print(data['cumulative_results']['2'].keys())
        sft_shot_means = extract_shots_scores(data['cumulative_results']['2'],score_idx)
        # acc = sft_shot_means[rollouts]
        # ax.plot(rollouts, acc, label="sft", marker=markers[0], color=deepmind_colors[0], ms=3)
        plt.plot(range(1,129), sft_shot_means, label="sft", color=deepmind_colors[1], ms=3)
        marker = [sft_shot_means[r-1] for r in rollouts]  # r-1 because list is 0-indexed
        plt.scatter(rollouts, marker, marker=markers[1], color=deepmind_colors[1], s=50, zorder=5)
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/old_score_novel_spec_compare"
    for idx,model in enumerate(model_names):
        for count,file in enumerate(shot_files[model]):
            label = file.split("global_step_")[-1]
            if "eval_results" in label:
                label = label.split("/")[0]
            else:
                label = label.split("_")[0]
            with open(file, 'r') as f:
                data = json.load(f)
            if file.endswith("eval_results.json"):
                data = clean_data(model,data)
            elif file in wrong_data:
                data = clean_data_2(data)
            # print(model)
            # print(data['cumulative_results']['2'].keys())
            shot_means = extract_shots_scores(data['cumulative_results']['2'],score_idx)
            # acc = shot_means[rollouts]
            # ax.plot(rollouts, acc, label=f"Step {step}", marker=markers[count+1], color=deepmind_colors[count+1], ms=3)
            plt.plot(range(1,129), shot_means, label=f"Model: {model} Step: {label}", color=deepmind_colors[idx+2], ms=3)
            marker = [shot_means[r-1] for r in rollouts]  # r-1 because list is 0-indexed
            plt.scatter(rollouts, marker, marker=markers[idx+2], color=deepmind_colors[idx+2], s=50, zorder=5)
            
    plt.xticks(rollouts, rollouts)
    plt.xlabel("Rollout Number")
    plt.ylabel("Novel Spec Rate")
    plt.ylim(0.0,0.2)
    plt.title("Novel Spec Rate vs. Rollout Number")

    plt.grid(True, linestyle='--', alpha=0.3)
    plt.legend(loc="right")
    plt.tight_layout()
    # plt.subplots_adjust(top=0.88)
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)
    plt.savefig(os.path.join(shots_output_dir,f"model_compare.pdf"))
    
def ablation_shots():
    wrong_data=[ "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset/scores_7-11-hour-11/global_step_40_scores_7-11-hour-11.json",
        "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score/scores_7-10-hour-22/saves_scores_7-10-hour-22.json"]

    model_names = [
        "kl_only",
        "entropy_only"
    ]
    labels = ["Subset Reward Model with KL", "Subset Reward Model with Entropy"]
    max_pow = 7
    powers = 2**np.arange(max_pow + 1)
    marker_indices = (powers - 1).tolist()
    colors = {'20':"#009E73", '80':"#D55E00"}
    
    fig, axes = plt.subplots(1, len(model_names), figsize=(4 * len(model_names), 4))
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/old_score_model_shot_compare"
    for idx,model in enumerate(model_names):
        for i, score_idx in enumerate([2]):
            ax = axes[idx]
            if i == 1:
                ax.set_ylim(0.4,1.0)
            elif i == 0:
                ax.set_ylim(0.1,0.7)
            for file in shot_files['sft']:
                with open(file, 'r') as f:
                    data = json.load(f)
                if file.endswith("eval_results.json"):
                    data = clean_data(model,data)
                elif file in wrong_data:
                    data = clean_data_2(data)
                # print(data['cumulative_results']['2'].keys())
                sft_shot_means = extract_shots_scores(data['cumulative_results']['2'],score_idx)
                # acc = sft_shot_means[rollouts]
                # ax.plot(rollouts, acc, label="sft", marker=markers[0], color=deepmind_colors[0], ms=3)
                ax.plot(range(1,129), sft_shot_means, label="sft", marker=markers[3], color=deepmind_colors[4], ms=3,markevery=marker_indices)
            for count,file in enumerate(shot_files[model]):
                label = file.split("global_step_")[-1]
                if "eval_results" in label:
                    label = label.split("/")[0]
                else:
                    label = label.split("_")[0]
                with open(file, 'r') as f:
                    data = json.load(f)
                if file.endswith("eval_results.json"):
                    data = clean_data(model,data)
                elif file in wrong_data:
                    data = clean_data_2(data)
                # print(model)
                # print(data['cumulative_results']['2'].keys())
                shot_means = extract_shots_scores(data['cumulative_results']['2'],score_idx)
                # acc = shot_means[rollouts]
                # ax.plot(rollouts, acc, label=f"Step {step}", marker=markers[count+1], color=deepmind_colors[count+1], ms=3)
                ax.plot(range(1,129), shot_means, label=f"Step {label}",marker=markers[count], color=colors[label], ms=3,markevery=marker_indices)
            
            ax.set_title(labels[idx],fontsize=12)
            ax.set_xlabel("Rollout Number ($log_2$ scale)",fontsize=11)
            if idx == 0 and i==1:
                ax.set_ylabel("Verification Rate",fontsize=11)
            elif idx == 0 and i==0:
                ax.set_ylabel("Subset Reward",fontsize=10)
            ax.grid(True, linestyle="--", alpha=0.3)
            # set grid only at certain rollouts
            # Remove log scale to show actual integer values
            ax.set_xscale('log', base=2)
            ax.set_xticks(powers, [str(p) for p in powers], fontsize=10)
            yticks =[0.1,0.2,0.3,0.4,0.5,0.6,0.7]
            ax.set_yticks(yticks,yticks,fontsize=10)

    plt.legend(loc="best",fontsize=10)

    fig.suptitle("Spec Superiority Rate Versus Rollout Number", fontsize=13)
    plt.tight_layout(rect=[0, 0, 1, 0.9])
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)
    plt.subplots_adjust(top=0.82)

    plt.savefig(os.path.join(shots_output_dir,f"ablation.pdf"))

def compare_shots():
    file_lists = [
        # "/nas/shared/sys2/chefengdi/eval_log/DLC-diversity_reward_qwen_3b_5k_sft_5k_rl_4rollout_0_1scale_5000_ref_0.1_clip_mean_1_kw_v3_0entropy_0.01kl_xh1/global_step_20/scores/scores_7-11-hour-20/global_step_20_scores_7-11-hour-20.json",
        # "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/new_score_diveristy_kl/scores_7-10-hour-10/global_step_40_scores_7-10-hour-10.json",
        # "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/new_score_diveristy_kl/scores_7-10-hour-10/global_step_20_scores_7-10-hour-10.json",
        
        # "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_kl/DLC-diversity_reward_qwen_3b_5k_sft_5k_rl_4rollout_0_1scale_5000_ref_0.085_clip_mean_1_kw_sim_v4_0.02entropy_0.01kl_xh2/global_step_40/eval_results.json",
        "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_xuhan_newest/scores/scores_7-12-hour-8/global_step_160_scores_7-12-hour-8.json",
        "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_xuhan_newest/scores/scores_7-12-hour-8/global_step_320_scores_7-12-hour-8.json",
        "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_40_scores_7-11-hour-17.json",
        "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/saves_scores_7-11-hour-17.json",
    ]

    wrong_data=[ "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset/scores_7-11-hour-11/global_step_40_scores_7-11-hour-11.json",
        "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score/scores_7-10-hour-22/saves_scores_7-10-hour-22.json"]

    model_names = [
        "naive",
        "subset",
        "entropy"
    ]
    colors = {'20':"#009E73", '80':"#D55E00"}
    labels = ["Verification Reward Model", "Subset Reward Model", "Subset Reward Model with KL and Entropy"]
    max_pow = 7
    powers = 2**np.arange(max_pow + 1)
    marker_indices = (powers - 1).tolist()
    
    fig, axes = plt.subplots(1, len(model_names), figsize=(4 * len(model_names), 4))
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/old_score_model_shot_compare"
    for idx,model in enumerate(model_names):
        for i, score_idx in enumerate([2]):
            ax = axes[idx]
            if i == 1:
                ax.set_ylim(0.4,1.0)
            elif i == 0:
                ax.set_ylim(0.1,0.7)
            for file in shot_files['sft']:
                with open(file, 'r') as f:
                    data = json.load(f)
                if file.endswith("eval_results.json"):
                    data = clean_data(model,data)
                elif file in wrong_data:
                    data = clean_data_2(data)
                # print(data['cumulative_results']['2'].keys())
                sft_shot_means = extract_shots_scores(data['cumulative_results']['2'],score_idx)
                # acc = sft_shot_means[rollouts]
                # ax.plot(rollouts, acc, label="sft", marker=markers[0], color=deepmind_colors[0], ms=3)
                ax.plot(range(1,129), sft_shot_means, label="sft", marker=markers[3], color=deepmind_colors[4], ms=3,markevery=marker_indices)
            for count,file in enumerate(shot_files[model]):
                label = file.split("global_step_")[-1]
                if "eval_results" in label:
                    label = label.split("/")[0]
                else:
                    label = label.split("_")[0]
                with open(file, 'r') as f:
                    data = json.load(f)
                if file.endswith("eval_results.json"):
                    data = clean_data(model,data)
                elif file in wrong_data:
                    data = clean_data_2(data)
                # print(model)
                # print(data['cumulative_results']['2'].keys())
                shot_means = extract_shots_scores(data['cumulative_results']['2'],score_idx)
                # acc = shot_means[rollouts]
                # ax.plot(rollouts, acc, label=f"Step {step}", marker=markers[count+1], color=deepmind_colors[count+1], ms=3)
                ax.plot(range(1,129), shot_means, label=f"Step {label}",marker=markers[count], color=colors[label], ms=3,markevery=marker_indices)

                # print(model,file)
                # print(shot_means)
            ax.set_title(labels[idx],fontsize=12)
            ax.set_xlabel("Rollout Number ($log_2$ scale)",fontsize=11)
            if idx == 0 and i==1:
                ax.set_ylabel("Verification Rate",fontsize=11)
            elif idx == 0 and i==0:
                ax.set_ylabel("Subset Reward",fontsize=11)
            ax.grid(True, linestyle="--", alpha=0.3)
            # set grid only at certain rollouts
            # Remove log scale to show actual integer values
            ax.set_xscale('log', base=2)
            ax.set_xticks(powers, [str(p) for p in powers], fontsize=10)
            yticks =[0.1,0.2,0.3,0.4,0.5,0.6,0.7]
            ax.set_yticks(yticks,yticks,fontsize=10)

    plt.legend(loc="best",fontsize=10)

    fig.suptitle("Spec Superiority Rate Versus Rollout Number", fontsize=13)
    plt.tight_layout(rect=[0, 0, 1, 0.9])
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)
    plt.subplots_adjust(top=0.82)

    plt.savefig(os.path.join(shots_output_dir,f"shot_compare.pdf"))

def compare_training_log():
    file_list = [
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/train_shot_compare-3B-new/xuhan/scores_7-12-hour-14/DLC-diversity_reward_qwen_3b_5k_sft_5k_rl_4rollout_0_1scale_5000_ref_0.1_clip_mean_1_kw_v3_xh1_scores_7-12-hour-14.json",
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/train_shot_compare-3B-new/scores_7-12-hour-13/3B_prevent_hacking_rollout_4_scores_7-12-hour-13.json",
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/train_shot_compare-3B-new/scores_7-12-hour-13/DLC-diversity_reward_qwen_3b_5k_sft_5k_rl_4rollout_0_1scale_5000_ref_0.1_clip_mean_1_kw_v3_0entropy_0.01kl_xh1_scores_7-12-hour-13.json",
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/train_shot_compare-3B-new/scores_7-12-hour-13/Subsetreward_entropy_3B_BoN4_entropy0.02_with_kl_scores_7-12-hour-13.json"
    ]

    model_names = [
        "xuhan_v3",
        "subset",
        "xuhan_v3_0entropy_0.01kl",
        "chuanhao_40",
        # "sft"
    ]
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/first_training_log_compare"
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)
    cumulative_scores = {}
    for file in file_list:
        model_name =  os.path.basename(file)
        cumulative_scores[model_name] ={}
        cumulative_scores[model_name]['cumulative_results'] = {}
        
        with open(file, 'r') as f:
            data = json.load(f)
        for step in data['cumulative_results'].keys():
            if "diversity" in model_name:
                cumulative_scores[model_name]['cumulative_results'][int(step)*5//2] = {}
                for shot_key in data['cumulative_results'][step].keys():
                    cumulative_scores[model_name]['cumulative_results'][int(step)*5//2][int(shot_key)] = data['cumulative_results'][step][shot_key]
            else:
                cumulative_scores[model_name]['cumulative_results'][int(step)] = {}
                for shot_key in data['cumulative_results'][step].keys():
                    cumulative_scores[model_name]['cumulative_results'][int(step)][int(shot_key)] = data['cumulative_results'][step][shot_key]
    shot_numbers = [1]
    global_steps = cumulative_scores[model_name]['cumulative_results'].keys()
    print(cumulative_scores.keys())
    plot_scores(cumulative_scores,global_steps, shot_numbers, shots_output_dir)

def move_files():
    curr_dir = "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity"
    file_dirs= [
        "DLC-diversity_reward_qwen_3b_5k_sft_5k_rl_4rollout_0_1scale_5000_ref_0.1_clip_mean_1_kw_v3_0.02entropy_0.01kl_xh1/global_step_20",
        "DLC-diversity_reward_qwen_3b_5k_sft_5k_rl_4rollout_0_1scale_5000_ref_0.1_clip_mean_1_kw_v3_0entropy_0.01kl_xh1/global_step_20"
    ]

    mv_dir = "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_kl"

    for file_dir in file_dirs:
        count = 0
        for folder in os.listdir(os.path.join(curr_dir, file_dir)):
            if not os.path.exists(os.path.join(mv_dir, file_dir,folder)):
                os.makedirs(os.path.join(mv_dir, file_dir,folder))
                num_files = 0
            else:
                num_files = len(os.listdir(os.path.join(mv_dir, file_dir,folder)))
            if folder.endswith(".json"):
                shutil.move(os.path.join(curr_dir, file_dir, folder), os.path.join(mv_dir, file_dir, folder))
            else:
                filelists = [int(x[:-4]) for x in os.listdir(os.path.join(curr_dir, file_dir,folder)) if x.endswith(".dfy") and x not in ["gt.dfy", "input.dfy"]]
                for idx in filelists:
                    num_file = idx + num_files * 10000
                    shutil.move(os.path.join(curr_dir, file_dir, folder, f"{idx}.dfy"), os.path.join(mv_dir, file_dir, folder, f"{num_file}.dfy"))
                    try:
                        shutil.move(os.path.join(curr_dir, file_dir, folder, f"out-{idx}.txt"), os.path.join(mv_dir, file_dir, folder, f"out-{num_file}.txt"))
                        shutil.move(os.path.join(curr_dir, file_dir, folder, f"err-{idx}.txt"), os.path.join(mv_dir, file_dir, folder, f"err-{num_file}.txt"))
                    except:
                        pass
                    num_files += 1
                    count+=1
                for file in os.listdir(os.path.join(curr_dir, file_dir,folder)):
                    shutil.move(os.path.join(curr_dir, file_dir, folder, file), os.path.join(mv_dir, file_dir, folder, file))
            print(f"move {count} files from {file_dir} to {mv_dir}")


def plot_saved_scores():
    file_dirs= [
        "/nas/shared/sys2/chefengdi/eval_log/3B_log_compare/kl/scores_7-10-hour-20/Subsetreward_entropy_3B_BoN4_entropy0.02_with_kl_scores_7-10-hour-20.json",
        # "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/new_score_diveristy_kl/scores_7-10-hour-16/global_step_20_scores_7-10-hour-16.json",
        # "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/new_score_diveristy_kl/scores_7-10-hour-10/global_step_20_scores_7-10-hour-10.json",
        # "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/new_score_diveristy_kl/scores_7-10-hour-10/global_step_40_scores_7-10-hour-10.json"
    ]
    names = ["baseline_40",
        "v_3_0.02entropy_0.01kl",
        "v_3_0entropy_0.01kl",
        "v_4_0.02entropy_0.01kl",
    ]
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/new_score_kl/shots_plot"

    cumulative_scores = {}
    for i, file_dir in enumerate(file_dirs):
        cumulative_scores[names[i]] = {}
        cumulative_scores[names[i]]['cumulative_results'] = {}
        with open(file_dir, 'r') as f:
            data = json.load(f)
        for step in data['cumulative_results'].keys():
            cumulative_scores[names[i]]['cumulative_results'][int(step)] = {}
            for shot_key in data['cumulative_results'][step].keys():
                cumulative_scores[names[i]]['cumulative_results'][int(step)][int(shot_key)] = data['cumulative_results'][step][shot_key]
    global_steps = cumulative_scores[names[0]]['cumulative_results'].keys()
    shot_numbers = [1]

    plot_scores(cumulative_scores, global_steps, shot_numbers, shots_output_dir)
    
    # plot_scores_vs_shots(cumulative_scores, global_steps, shot_numbers, shots_output_dir,target_steps=global_steps)

if __name__ == "__main__":
    # plot_saved_scores()
    # move_files()

    # compare_shots()
    # compare_training_log()
    # check_GPT()

    # plot_novel_spec()
    ablation_shots()
    # qwen_coder()
    