# 128 score
shot_files = {
"naive":
[  
    "eval_logs/Jul_report_results/report_shots/final_scores/naive_1/scores_7-16-hour-7/global_step_20_scores_7-16-hour-7.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/naive_1/scores_7-16-hour-7/global_step_40_scores_7-16-hour-7.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/naive_2/scores_7-16-hour-7/global_step_160_scores_7-16-hour-7.json",
    "eval_logs/Jul_report_results/report_shots/final_scores/naive_2/scores_7-16-hour-7/global_step_80_scores_7-16-hour-7.json",
],
"subset":[  
    "eval_logs/Jul_report_results/report_shots/final_scores/subset_1/scores_7-16-hour-7/global_step_20_scores_7-16-hour-7.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/subset_1/scores_7-16-hour-7/global_step_40_scores_7-16-hour-7.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/subset_2/scores_7-16-hour-7/global_step_160_scores_7-16-hour-7.json",
    "eval_logs/Jul_report_results/report_shots/final_scores/subset_2/scores_7-16-hour-7/global_step_80_scores_7-16-hour-7.json",
],
"entropy":[
    "eval_logs/Jul_report_results/report_shots/final_scores/entropy_1/scores_7-16-hour-14/global_step_20_scores_7-16-hour-14.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/entropy_1/scores_7-16-hour-14/global_step_40_scores_7-16-hour-14.json",
    "eval_logs/Jul_report_results/report_shots/final_scores/entropy_2/scores_7-16-hour-14/global_step_80_scores_7-16-hour-14.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/entropy_2/scores_7-16-hour-14/global_step_160_scores_7-16-hour-14.json",
],
"entropy_only":[  
    "eval_logs/Jul_report_results/report_shots/final_scores/entropy_only_1/scores_7-16-hour-7/global_step_20_scores_7-16-hour-7.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/entropy_only_1/scores_7-16-hour-7/global_step_40_scores_7-16-hour-7.json",
    "eval_logs/Jul_report_results/report_shots/final_scores/entropy_only_2/scores_7-16-hour-14/global_step_80_scores_7-16-hour-14.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/entropy_only_2/scores_7-16-hour-14/global_step_160_scores_7-16-hour-14.json",
],
"kl_only":[
    "eval_logs/Jul_report_results/report_shots/final_scores/kl_only_1/scores_7-16-hour-14/global_step_20_scores_7-16-hour-14.json",
    "eval_logs/Jul_report_results/report_shots/final_scores/kl_only_2/scores_7-16-hour-11/global_step_80_scores_7-16-hour-11.json",
    # "eval_logs/Jul_report_results/report_shots/final_scores/kl_only_2/scores_7-15-hour-19/global_step_160_scores_7-15-hour-19.json"
],
"sft":[
    "eval_logs/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/saves_scores_7-11-hour-17.json",
    ]
}

diveristy_files = {
    "naive":"eval_logs/analysis/log_analysis_rollout_3B_reward_naive_0513_v5_40step_all_eval/list_mean.json",
    "subset":"eval_logs/analysis/log_analysis_rollout_3B_Subsetreward_20step_partial_all_eval/list_mean.json",
    "entropy": "eval_logs/analysis/log_analysis_rollout_Subsetreward_entropy_3B_BoN4_entropy0.02_with_kl_40step_all_eval/list_mean.json",
    "sft":"eval_logs/analysis/log_analysis_rollout_sft_all_eval/list_mean.json",
}

old_shot_files = {
"naive":
[
    "eval_logs/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_20/eval_results.json",
    # "eval_logs/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_40/eval_results.json",
    "eval_logs/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_80/eval_results.json",
],
"subset":[
    # "eval_logs/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_20/eval_results.json",
    # "eval_logs/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_40/eval_results.json",
    # "eval_logs/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_80/eval_results.json",
    "eval_logs/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_160/eval_results.json",
],
"entropy":[
    # "eval_logs/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_20_scores_7-11-hour-17.json",
    "eval_logs/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_40_scores_7-11-hour-17.json",
    # "eval_logs/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_80_scores_7-11-hour-17.json",
],
"entropy_only":[
    "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_20/eval_results.json",
    "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_40/eval_results.json",
    "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_80/eval_results.json",
    # "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_160/eval_results.json",
],
"kl_only":[
    "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl/global_step_20/eval_results.json",
    "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl/global_step_40/eval_results.json",
    "eval_logs/DLC_naive_128/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl/global_step_80/eval_results.json",
],
"sft":[
    "eval_logs/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/saves_scores_7-11-hour-17.json",
    ]
}