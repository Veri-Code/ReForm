import os
from verl.inference.plot import *
import json
import matplotlib.pyplot as plt
import numpy as np
import argparse

parse_args = argparse.ArgumentParser()
parse_args.add_argument("--file_list", type=str, nargs='+', help="file list")
parse_args.add_argument("--training_length", type=int, default=20, help="training length")
file_list_all = parse_args.parse_args().file_list


index = 1

model_names = [
    "0.5B",
    "1.5B",
    "3B",
    "7B",
    "14B"

    # "sft"
]

file_list = file_list_all
# file_list = file_list_all[index::5]
print(file_list)

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
        dataset_len = len(cumulative_results[2][1])
        print("dataset_len: ", dataset_len)
        # Extract means and stds for this score component
        step_means = []
        


        for step in global_steps:
            shot_keys = list(cumulative_results[step].keys())
            shot_keys = [int(shot_key) for shot_key in shot_keys]


            

            scores = cumulative_results[step][1]
            scores = np.array(scores)
            scores = np.where(scores == -1, 0, scores)
            mean_score = np.mean(scores[:, i])
            step_means.append(mean_score)

        
        output.append(step_means)
    full_output.append(output)

metric_names = [
    "Validation Rate",
    "Verification Rate",
    "Spec Superiority Rate"
]
num_models = len(file_list_all)
for i in range(3):
    for j in range(len(file_list_all)):
        # diff = full_output[i][j][0] - full_output[i][2][0]
        # full_output[i][j] = [x - diff for x in full_output[i][j]]

        name = metric_names[i]
        score = max(full_output[i][j])
        print(f"{name} for model {j}: {score}")

# exit()
deepmind_colors = [
    "#1A1A1A",  
    "#0072B2",  
    "#009E73",  
    "#D55E00",  
    "#CC79A7",  
    "#F0E442",  
    "#56B4E9",  
]

# metric_names = [
#     "Validation Rate",
#     "Verification Rate",
#     "Spec Superiority Rate"
# ]

# labels = ["verification", "subset", "subset+KL+entropy"]
labels = [f"model {j}" for j in range(num_models)]

markers = ['o', 's', '^', 'v', 'D', 'p', '*', 'x', '+', 'h']
training_length = parse_args.parse_args().training_length
x = range(0, training_length * 2, 2)
fig, axes = plt.subplots(1, 3, figsize=(12, 4))
for i in range(3):
    ax = axes[i]
    for j in range(num_models):
        ax.plot(x, full_output[i][j][:training_length], label=labels[j], marker=markers[j], markersize=3, markevery=5, color=deepmind_colors[j+1])
    ax.set_xlabel("Training Steps")
    ax.set_ylabel(metric_names[i])
    ax.grid(True, linestyle="--", alpha=0.3)
plt.legend(loc="best")
fig.suptitle(f"{model_names[index]}-pass@1 across training steps", fontsize=14)
plt.tight_layout(rect=[0, 0, 1, 0.9])
plt.subplots_adjust(top=0.88)
plt.savefig(f"test.png")
