import numpy as np
import matplotlib.pyplot as plt
import os
from verl.inference.plot import plot_scores, plot_scores_vs_shots, compute_cumulative_binary_scores
from concurrent.futures import ProcessPoolExecutor, as_completed
from verl.inference.reward_score.inference_reward import compute_subset_score
from verl.inference.log_dir import shot_files,diveristy_files
from verl.utils.reward_score.condition_comparison_fixed import *

deepmind_colors = [
    "#1A1A1A",  
    "#D55E00", #orange verification
    "#56B4E9",  # light blue subset
    "#009E73",  # green entropy
    "#0072B2",  # blue SFT
    "#CC79A7",  # pink
    "#F0E442",  # yellow
]

shot_one_all_datasets = {
    "eval":{
        "gpt-4o":[0.4609375 , 0.11328125, 0.0625],
        "sft":[0.9453125 , 0.58789062, 0.30664062],
        "RL": [0.98242188, 0.80273438, 0.5 ],
    },
    "dafny":{
        "gpt-4o":[0.76, 0.39, 0.22],
        "sft":[0.89, 0.41, 0.26],
        "RL": [0.94, 0.58, 0.42 ],
    },
    "autospec":{
        "gpt-4o":[0.64, 0.003, 0.0],
        "sft":[0.77, 0.06, 0.027],
        "RL": [0.93, 0.12, 0.04],
    }
}

score_lists = ["Validation Rate", "Verification Rate", "Spec Superiority Rate"]


# def load_score_lists():
#     models = ["naive","sft","subset","entropy"]
#     steps = [40,0,20,40]

#     for model,step in zip(models,steps):
#         print(model,step)
#         diversity_file = diveristy_files[model]
#         with open(diversity_file, 'r') as f:
#             diversity_data = json.load(f)
#         print(diversity_data.keys())
#         shot_file_lists = shot_files[model]
#         for shot_file in shot_file_lists:
#             if str(step) in shot_file or model == "sft":
#                 with open(shot_file, 'r') as f:
#                     shot_data = json.load(f)
#                 print(np.mean(shot_data['cumulative_results']['2']['128'],axis=0))

def plot_all_score_radars():
    """Create radar plots for each score type across all datasets and models."""
    
    # Create output directory
    shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/radar"
    if not os.path.exists(shots_output_dir):
        os.makedirs(shots_output_dir)
    
    # Define categories (datasets) and models
    categories = ['Out-Of-Domain Evaluation', 'In-Domain Evaluation', 'DafnyBench']
    dataset_keys = ['autospec', 'eval', 'dafny']
    models = ['gpt-4o', 'sft', 'RL']
    colors = ["#CC79A7", "#0072B2", "#009E73"]
    
    # Create a figure with subplots for each score
    fig, axes = plt.subplots(1, 3, figsize=(18, 8), subplot_kw=dict(projection='polar'))
    
    for score_idx, (ax, score_name) in enumerate(zip(axes, score_lists)):
        # Compute angles and close the loop
        N = len(categories)
        angles = np.linspace(0, 2*np.pi, N, endpoint=False).tolist()
        angles += angles[:1]
        
        # Set up the polar plot
        ax.set_theta_offset(np.pi/2)
        ax.set_theta_direction(-1)
        
        # Remove default labels and add custom rotated labels
        ax.set_xticks(angles[:-1])
        ax.set_xticklabels([])
        
        # Set different radial limits for each score type
        if score_idx == 0:
            # Validation Rate
            ax.set_ylim(0, 1.0)
            ax.set_yticks([0.2, 0.4, 0.6, 0.8, 1.0])
            label_radius = 1.15
        elif score_idx == 1:
            # Verification Rate
            ax.set_ylim(0, 0.8)
            ax.set_yticks([0.2, 0.4, 0.6, 0.8])
            label_radius = 0.92
        elif score_idx == 2:
            # Spec Superiority Rate
            ax.set_ylim(0, 0.5)
            ax.set_yticks([0.1, 0.2, 0.3, 0.4, 0.5])
            label_radius = 0.58
        
        ax.set_rlabel_position(180/N)
        
        # Manually place each label with proper rotation and positioning
        for angle, category in zip(angles[:-1], categories):
            angle_deg = np.degrees(angle)
            if angle_deg == 0:
                rotation = 0
                ha = 'center'
                va = 'top'
            elif angle_deg > 180:
                rotation = angle_deg + 90
                ha = 'center'
                va = 'top'
            else:
                rotation = angle_deg - 90
                ha = 'center'
                va = 'top'
            
            # Place text at calculated radius outside the chart
            ax.text(angle, label_radius, category, 
                   rotation=rotation, ha=ha, va=va, fontsize=14)
        
        # Plot data for each model
        for model_idx, (model, color) in enumerate(zip(models, colors)):
            # Extract scores for this model across all datasets for the current score type
            model_scores = []
            for dataset_key in dataset_keys:
                model_scores.append(shot_one_all_datasets[dataset_key][model][score_idx])
            
            # Close the loop for radar plot
            model_scores_closed = model_scores + model_scores[:1]
            
            # Plot the data
            ax.plot(angles, model_scores_closed, 'o-', linewidth=3, 
                   label=model.upper(), color=color, markersize=8)
            ax.fill(angles, model_scores_closed, alpha=0.15, color=color)
        
        # Set title for this subplot
        ax.set_title(score_name, y=1.15, fontsize=18, fontweight='bold')
        
        # Add score labels for Out-Of-Domain Evaluation on the last chart only
        if score_idx==2:  # Spec Superiority Rate chart
            # Find the angle for Out-Of-Domain Evaluation (first category)
            out_domain_angle = angles[0]  # First angle corresponds to first category
            
            # Add labels for each model's score at Out-Of-Domain Evaluation
            for model_idx, (model, color) in enumerate(zip(models, colors)):
                score_value = shot_one_all_datasets['autospec'][model][score_idx]
                
                # Position the label slightly outside the data point
                label_offset = 0.1 + (model_idx * 0.055)  # Stagger labels to avoid overlap
                
                ax.text(out_domain_angle, score_value + label_offset, 
                       f'{score_value:.3f}', 
                       ha='center', va='bottom', fontsize=12, 
                       color=color, fontweight='bold',
                       bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8, edgecolor=color))
        if score_idx==1:  # Spec Superiority Rate chart
            # Find the angle for Out-Of-Domain Evaluation (first category)
            out_domain_angle = angles[0]  # First angle corresponds to first category
            
            # Add labels for each model's score at Out-Of-Domain Evaluation
            for model_idx, (model, color) in enumerate(zip(models, colors)):
                score_value = shot_one_all_datasets['autospec'][model][score_idx]
                
                # Position the label slightly outside the data point
                label_offset = 0.25 + (model_idx * 0.055)  # Stagger labels to avoid overlap
                
                ax.text(out_domain_angle, score_value + label_offset, 
                       f'{score_value:.3f}', 
                       ha='center', va='bottom', fontsize=12, 
                       color=color, fontweight='bold',
                       bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8, edgecolor=color))
        
        # Add legend only to the last subplot
        if score_idx == 2:
            ax.legend(loc='upper right', bbox_to_anchor=(1.4, 1.15), fontsize=14)
    
    # Add overall title
    fig.suptitle('Performance Comparison Across Tasks and Models', fontsize=22, y=0.95, fontweight='bold')
    
    # Save the plot
    plt.tight_layout()
    plt.subplots_adjust(top=0.87)
    # plt.savefig(os.path.join(shots_output_dir, 'all_scores_radar.pdf'), dpi=300, bbox_inches='tight')
    plt.savefig(os.path.join(shots_output_dir, 'all_scores_radar.pdf'), dpi=300, bbox_inches='tight')
    
    # Show the plot
    plt.show()

# def radar():
#     # 1. Define categories and data
#     categories = ['In-Domain Evaluation', 'DafnyBench', 'Out-Of-Domain Evaluation']
#     RL_scores = [44.5, 23.1, 44.0]
#     GPT_scores = [10.1, 7.5, 6.0]
#     base_scores = [0.5, 0.1, 0.4]
#     SFT_scores = [24.5, 13.1, 24.0]

#     # 2. Compute angles and close the loop
#     N = len(categories)
#     angles = np.linspace(0, 2*np.pi, N, endpoint=False).tolist()
#     angles += angles[:1]

#     RL = RL_scores + RL_scores[:1]
#     GPT = GPT_scores + GPT_scores[:1]
#     base = base_scores + base_scores[:1]
#     SFT = SFT_scores + SFT_scores[:1]

#     # 3. Plot
#     fig, ax = plt.subplots(figsize=(8, 8), subplot_kw=dict(projection='polar'))

#     # Rotate so the first axis is at the top
#     ax.set_theta_offset(np.pi/2)
#     ax.set_theta_direction(-1)

#     # Draw one axis per variable + add labels
#     ax.set_xticks(angles[:-1])
#     # Remove default labels and add custom rotated labels
#     ax.set_xticklabels([])

#     # Manually place each label with proper rotation
#     for angle, category in zip(angles[:-1], categories):
#         # Convert angle to degrees
#         angle_deg = np.degrees(angle)
#         if angle_deg == 0:
#             rotation = 0
#             ha = 'center'
#             va = 'top'
#         elif angle_deg > 180:
#             rotation = angle_deg + 90
#             ha = 'center'
#             va = 'top'
#         else:
#             rotation = angle_deg - 90
#             ha = 'center'
#             va = 'top'
#         print(category,"LLL",rotation,"LLL", angle_deg)
#         # Place text at a fixed distance outside the chart (radius = 55, which is beyond ylim of 50)
#         ax.text(angle, 55, category, 
#             rotation=rotation, ha=ha, va=va, fontsize=11)

#     # Draw ylabels
#     ax.set_rlabel_position(180/N)
#     ax.set_yticks([10, 20, 30, 40, 50])
#     ax.set_ylim(0, 50)

#     # Plot data with different colors and styles
#     ax.plot(angles, RL, 'o-', linewidth=2, label='RL', color='red')
#     ax.fill(angles, RL, alpha=0.25, color='red')

#     ax.plot(angles, SFT, 'o-', linewidth=2, label='SFT', color='blue')
#     ax.fill(angles, SFT, alpha=0.25, color='blue')

#     ax.plot(angles, GPT, 'o-', linewidth=2, label='GPT', color='green')
#     ax.fill(angles, GPT, alpha=0.25, color='green')

#     ax.plot(angles, base, 'o-', linewidth=2, label='Base', color='orange')
#     ax.fill(angles, base, alpha=0.25, color='orange')

#     # Create output directory
#     shots_output_dir = "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/radar"
#     if not os.path.exists(shots_output_dir):
#         os.makedirs(shots_output_dir)

#     # Add legend and title
#     plt.title('Pass@8 Spec Superiority Rate Across Tasks', y=1.08, fontsize=14)
#     ax.legend(loc='upper right', bbox_to_anchor=(1.2, 1.1))

#     # Save the plot
#     plt.tight_layout()
#     plt.savefig(os.path.join(shots_output_dir, 'report_plot.pdf'), dpi=300, bbox_inches='tight')
#     plt.savefig('report_plot.png', dpi=300, bbox_inches='tight')

#     # Show the plot
#     plt.show()

if __name__ == "__main__":
    plot_all_score_radars()