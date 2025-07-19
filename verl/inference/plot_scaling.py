import matplotlib.pyplot as plt
import numpy as np
import os
import json
deepmind_colors = [
    "#1A1A1A",  
    "#D55E00", #orange verification
    "#CC79A7",  # pink subset
    "#009E73",  # green entropy
    "#0072B2",  # blue SFT
    "#56B4E9",  # light blue 
    "#F0E442",  # yellow
]

metric_names = [
    "Validation Rate （%）",
    "Verification Rate （%）",
    "Spec Superiority Rate （%）"
]
labels = ["verification", "subset", "subset+KL+entropy", "sft"]
markers = ['o', 's', '^', 'v', 'D', 'p', '*', 'x', '+', 'h']
def model_scale():
    model_sizes = ['0.5B', '1.5B', '3B', '7B', '14B']
    x = range(5)
    full_output = [
        # Parse rate
        [
            [99.2, 98.8, 98.8, 99.6, 99.4],
            [96.3, 97.5, 97.7, 98.4, 99.0],
            [97.1, 94.3, 98.0, 98.2, 99.0],
            [82.0, 85.0, 87.0, 89.0 ,76.7],
        ],
        # Verification rate
        [
            [92.8, 86.0 , 85.2, 89.1, 92.6],
            [65.8, 72.4, 75.0, 78.1, 85.9],
            [60.9, 59.0, 73.4 , 74.0, 84.0],
            [30.3, 39.0, 46.0, 49.0, 7.0],
        ],
        # Spec superiority rate
        [
            [20.7 , 27.0, 30.7, 30.7, 37.3],
            [30.1, 40.4, 44.7, 49.8, 55.3],
            [28.5, 31.8, 42.0, 44.1, 53.9],
            [17.6, 22.0, 26.0, 27.1, 3.4],
        ],
    ]

    full_output = np.array(full_output)
    full_output = full_output.tolist()

    fig, axes = plt.subplots(1, 3, figsize=(12, 4))
    for i in range(3):
        ax = axes[i]
        for j in range(4):
            ax.plot(x, full_output[i][j], label=labels[j], marker=markers[j], markersize=3, markevery=1, color=deepmind_colors[j+1])
        ax.set_xlabel("Model Size",fontsize=11)
        ax.set_xticks(x, model_sizes,fontsize=10)
        ax.set_yticks(np.arange(0.0, 1.05, 0.1),[str(x) for x in np.arange(0.0, 1.05, 0.1).round(1).tolist()],fontsize=10)
        ax.set_ylabel(metric_names[i],fontsize=11)
        ax.set_ylim(0.0, 1.05)
        ax.set_title(metric_names[i],fontsize=12)
        ax.grid(True, linestyle="--", alpha=0.3)
    plt.legend(loc="best",fontsize=10)
    fig.suptitle(f"Pass@1 Results Across Model Sizes", fontsize=13)
    plt.tight_layout(rect=[0, 0, 1, 0.9])
    plt.subplots_adjust(top=0.84)
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/model_size"
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)

    plt.savefig(os.path.join(shots_output_dir, "pass@1-across-model-size.pdf"))

def ablation():
    model_names = [
        'subset+entropy', 
        'subset+KL', 
        'subset+KL+entropy'
    ]
    folder_names = [
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/pass_one/scores_7-16-hour-0/3B_BoN4_entropy_only_scores_7-16-hour-0.json",
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/pass_one/scores_7-16-hour-0/3B_BoN4_kl_only_scores_7-16-hour-0.json",
        "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/pass_one/scores_7-16-hour-19/3B_BoN4_entropy_scores_7-16-hour-19.json"
    ]
    colors = [
        "#56B4E9",  # light blue
        "#0072B2",  # blue SFT
        "#009E73",  # green entropy
    ]

    plt.figure(figsize=(5,4))
    
    for idx, folder_name in enumerate(folder_names):
        cumulative_scores = json.load(open(folder_name, "r"))
        scores = []
        print(cumulative_scores['cumulative_results'].keys())
        for step in cumulative_scores['cumulative_results'].keys():
            score = cumulative_scores['cumulative_results'][step]['1']
            score = np.array(score)
            score = np.where(score == -1, 0, score)
            score = score[:,2]
            scores.append(np.mean(score))
        training_length = len(scores)
        x = range(0, training_length * 2, 2)
        plt.plot(x, scores, label=model_names[idx], marker=markers[idx], markersize=3, markevery=20, color=colors[idx])
    plt.grid(True, linestyle="--", alpha=0.3)
    plt.legend(loc="best",fontsize=10)
    plt.xlabel("Training Steps",fontsize=10)
    plt.ylabel("Spec Superiority Rate （%）",fontsize=10)
    plt.title("Spec Superiority Rate Versus Training Steps",fontsize=12)
    plt.tight_layout(rect=[0, 0, 1, 0.9])
    plt.subplots_adjust(top=0.8)
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/final_ablation"
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)

    plt.savefig(os.path.join(shots_output_dir, "pass@1-ablation.pdf"))

if __name__ == "__main__":
    # model_scale()
    ablation()
# 单图
# model_sizes = ['0.5B', '1.5B', '3B', '7B', '14B']
# x = np.arange(len(model_sizes))

# curve1 = [59, 70, 75, 79, 81]
# curve2 = [51, 62, 66, 77, 79]
# curve3 = [47, 61, 68, 69, 76]

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


# 多图
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