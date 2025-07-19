import os
from verl.inference.plot import *
import json
import matplotlib.pyplot as plt
import numpy as np
def compare_training_log():
    file_list_all = [
        "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward/scores_7-13-hour-13/3B_prevent_hacking_rollout_4_scores_7-13-hour-13.json",
        "/nas/shared/sys2/liyizhi/folder-0709/eval_log/entropy_kl/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl_scores_7-15-hour-1.json",
        "/nas/shared/sys2/liyizhi/folder-0709/eval_log/entropy_kl/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl_scores_7-15-hour-1.json",
        "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward_kl_entropy/scores_7-12-hour-20/Subsetreward_entropy_3B_BoN4_entropy0.02_with_kl_scores_7-12-hour-20.json"
        # naive reward
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/naive_reward_subset_reward/scores_7-12-hour-0/DLC_4nodes_0.5B_reward_naive_0513_scores_7-12-hour-0.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/naive_reward_subset_reward/scores_7-12-hour-0/DLC_4nodes_1.5B_reward_naive2_scores_7-12-hour-0.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/naive_reward_subset_reward/scores_7-12-hour-0/DLC_4nodes_3B_reward_naive_0513_v5_scores_7-12-hour-0.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/naive_reward_subset_reward/scores_7-12-hour-0/DLC_4nodes_7B_reward_naive_0513_scores_7-12-hour-0.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/naive_reward_subset_reward/scores_7-12-hour-0/DLC_4nodes_14B_reward_naive_v4_scores_7-12-hour-0.json",

        # subset reward
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward/scores_7-13-hour-13/grpo_5ksft_0.5B_BoN4_prevent_hacking_v3_0705_9pm_scores_7-13-hour-13.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward/scores_7-13-hour-13/grpo_5ksft_1.5B_BoN4_prevent_hacking_v3_0705_9pm_scores_7-13-hour-13.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward/scores_7-13-hour-13/3B_prevent_hacking_rollout_4_scores_7-13-hour-13.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward/scores_7-13-hour-13/7B_prevent_kl0_lr1e-5_BoN4_scores_7-13-hour-13.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward/scores_7-13-hour-13/fengdi_grpo_5ksft_14B_prevent_hacking_v3_0622_11pm_scores_7-13-hour-21.json",

        # kl_entropy
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward_kl_entropy/scores_7-12-hour-20/Subsetreward_entropy_0.5B_BoN4_entropy0.02_with_kl_scores_7-12-hour-20.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward_kl_entropy/scores_7-12-hour-20/Subsetreward_entropy_1.5B_BoN4_entropy0.02_with_kl_scores_7-12-hour-20.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward_kl_entropy/scores_7-12-hour-20/Subsetreward_entropy_3B_BoN4_entropy0.02_with_kl_scores_7-12-hour-20.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward_kl_entropy/scores_7-12-hour-20/Subsetreward_entropy_7B_BoN4_entropy0.02_with_kl_true_scores_7-13-hour-21.json",
        # "/nas/shared/sys2/liyizhi/folder-0709/eval_log/subset_reward_kl_entropy/scores_7-12-hour-20/Subsetreward_entropy_14B_BoN4_entropy0.02_with_kl_scores_7-14-hour-0.json"
    ]

    # index = 1
    # model_names = [
    #     "0.5B",
    #     "1.5B",
    #     "3B",
    #     "7B",
    #     "14B"

    #     # "sft"
    # ]
    # model_names = [
    #     ""
    # ]
    file_list = file_list_all
    # print(file_list)

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

    global_steps = cumulative_scores[model_name]['cumulative_results'].keys()
    print(cumulative_scores.keys())


    exp_names = list(cumulative_scores.keys())
    
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
    


        
        # Plot each score component
    # for i, score_name in enumerate(score_names):

    full_output = []
    for i in range(3):
        output = []
        # Plot each experiment using consistent colors
        for exp_name, exp_data in cumulative_scores.items():
            global_steps = sorted(list(exp_data['cumulative_results'].keys()))
            print("global_steps: ", global_steps)
            cumulative_results = exp_data['cumulative_results']
            
            # Extract means and stds for this score component
            step_means = []
            for step in global_steps:
                shot_keys = list(cumulative_results[step].keys())
                shot_keys = [int(shot_key) for shot_key in shot_keys]
                if True:
                    # scores = cumulative_results[step][str(shot)]
                    scores = cumulative_results[step][1]
                    scores = np.array(scores)
                    scores = np.where(scores == -1, 0, scores)
                    mean_score = np.mean(scores[:, i])
                    step_means.append(mean_score)

            
            output.append(step_means)
        full_output.append(output)

    deepmind_colors = [
        "#1A1A1A",  
        "#0072B2",  
        "#009E73",  
        "#D55E00",  
        "#CC79A7",  
        "#F0E442",  
        "#56B4E9",  
    ]

    metric_names = [
        "Validation Rate",
        "Verification Rate",
        "Spec Superiority Rate"
    ]

    # labels = ["verification", "subset", "subset+KL+entropy"]
    labels = ["subset", "subset+entropy","subset+KL", "subset+KL+entropy"]

    markers = ['o', 's', '^', 'v', 'D', 'p', '*', 'x', '+', 'h']
    training_length = 40
    x = range(0, training_length * 2, 2)
    fig, axes = plt.subplots(1, 3, figsize=(12, 4))
    for i in range(3):
        ax = axes[i]
        for j in range(4):
            ax.plot(x, full_output[i][j][:training_length], label=labels[j], marker=markers[j], markersize=3, markevery=5, color=deepmind_colors[j+1])
        ax.set_xlabel("Training Steps")
        ax.set_ylabel(metric_names[i])
        ax.grid(True, linestyle="--", alpha=0.3)
    plt.legend(loc="best")
    fig.suptitle(f"Ablation of KL and Entropy", fontsize=14)
    plt.tight_layout(rect=[0, 0, 1, 0.9])
    plt.subplots_adjust(top=0.88)
    plt.savefig(f"Ablation-pass@1-across-training-steps.pdf")
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



    # # 单图
    # model_sizes = ['0.5B', '1.5B', '3B', '7B', '14B']
    # # x = np.arange(len(model_sizes))


    # training_length = 31
    # marking_points = [x for x in range(training_length) if x % 5 == 0]

    # x = output[0][:training_length]
    # x = [y-2 for y in x]

    # curves = [output[1][:training_length], output[3][:training_length], output[5][:training_length], output[7][:training_length], output[9][:training_length]]



    # plt.figure(figsize=(8, 5))
    # plt.plot(x, curves[0], label='0.5B', marker=markers[1], color=deepmind_colors[1], markevery=marking_points)
    # plt.plot(x, curves[1], label='1.5B', marker=markers[2], color=deepmind_colors[2], markevery=marking_points)
    # plt.plot(x, curves[2], label='3B',   marker=markers[3], color=deepmind_colors[3], markevery=marking_points)
    # plt.plot(x, curves[3], label='7B',   marker=markers[4], color=deepmind_colors[4], markevery=marking_points)
    # plt.plot(x, curves[4], label='14B',  marker=markers[5], color=deepmind_colors[5], markevery=marking_points)

    # # plt.xticks(x, model_sizes)
    # plt.xlabel("Training Steps")
    # plt.ylabel("Strength-To-GT")
    # plt.title("Strength-To-GT vs. Training Steps")

    # plt.grid(True, linestyle='--', alpha=0.3)
    # plt.legend(loc="lower right")
    # plt.tight_layout()
    # plt.savefig("naive_reward_training_curve_subset_reward.png")
    # plt.savefig("subset_reward_training_curve_subset_reward.png")
    # plt.savefig("kl_entropy_training_curve_subset_reward.png")


    # 多图

    # print(len(output))
    # print(output[0])
    # print(output[1])
    # exit()

    # keep 160 steps
    # rollouts = output[0][:80]


    # model_sizes = ['1.5B', '3B', '7B']

    # ckpt_steps = [40, 80, 120]
    # rollouts = [1, 2, 4, 8, 16, 32]

    # np.random.seed(0)
    # data = 
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

compare_training_log()