# 128 score
shot_files = {
"naive":
[  
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/naive_1/scores_7-16-hour-7/global_step_20_scores_7-16-hour-7.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/naive_1/scores_7-16-hour-7/global_step_40_scores_7-16-hour-7.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/naive_2/scores_7-16-hour-7/global_step_160_scores_7-16-hour-7.json",
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/naive_2/scores_7-16-hour-7/global_step_80_scores_7-16-hour-7.json",
],
"subset":[  
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/subset_1/scores_7-16-hour-7/global_step_20_scores_7-16-hour-7.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/subset_1/scores_7-16-hour-7/global_step_40_scores_7-16-hour-7.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/subset_2/scores_7-16-hour-7/global_step_160_scores_7-16-hour-7.json",
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/subset_2/scores_7-16-hour-7/global_step_80_scores_7-16-hour-7.json",
],
"entropy":[
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_1/scores_7-16-hour-14/global_step_20_scores_7-16-hour-14.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_1/scores_7-16-hour-14/global_step_40_scores_7-16-hour-14.json",
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_2/scores_7-16-hour-14/global_step_80_scores_7-16-hour-14.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_2/scores_7-16-hour-14/global_step_160_scores_7-16-hour-14.json",
],
"entropy_only":[  
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_only_1/scores_7-16-hour-7/global_step_20_scores_7-16-hour-7.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_only_1/scores_7-16-hour-7/global_step_40_scores_7-16-hour-7.json",
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_only_2/scores_7-16-hour-14/global_step_80_scores_7-16-hour-14.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/entropy_only_2/scores_7-16-hour-14/global_step_160_scores_7-16-hour-14.json",
],
"kl_only":[
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/kl_only_1/scores_7-16-hour-14/global_step_20_scores_7-16-hour-14.json",
    "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/kl_only_2/scores_7-16-hour-11/global_step_80_scores_7-16-hour-11.json",
    # "/nas/shared/sys2/chefengdi/eval_log/Jul_report_results/report_shots/final_scores/kl_only_2/scores_7-15-hour-19/global_step_160_scores_7-15-hour-19.json"
],
"sft":[
    "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/saves_scores_7-11-hour-17.json",
    ]
}

diveristy_files = {
    "naive":"/cpfs04/user/huangxuhan_p/log_analysis_rollout_3B_reward_naive_0513_v5_40step_all_eval/list_mean.json",
    "subset":"/cpfs04/user/huangxuhan_p/log_analysis_rollout_3B_Subsetreward_20step_partial_all_eval/list_mean.json",
    "entropy": "/cpfs04/user/huangxuhan_p/log_analysis_rollout_Subsetreward_entropy_3B_BoN4_entropy0.02_with_kl_40step_all_eval/list_mean.json",
    "sft":"/cpfs04/user/huangxuhan_p/log_analysis_rollout_sft_all_eval/list_mean.json",
}

old_shot_files = {
"naive":
[
    "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_20/eval_results.json",
    # "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_40/eval_results.json",
    "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_80/eval_results.json",
],
"subset":[
    # "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_20/eval_results.json",
    # "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_40/eval_results.json",
    # "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_80/eval_results.json",
    "/nas/shared/sys2/chefengdi/eval_log/DLC_subset_diversity_3B/3B_prevent_hacking_rollout_4/global_step_160/eval_results.json",
],
"entropy":[
    # "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_20_scores_7-11-hour-17.json",
    "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_40_scores_7-11-hour-17.json",
    # "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/global_step_80_scores_7-11-hour-17.json",
],
"entropy_only":[
    "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_20/eval_results.json",
    "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_40/eval_results.json",
    "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_80/eval_results.json",
    # "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_entropy0.01_without_kl/global_step_160/eval_results.json",
],
"kl_only":[
    "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl/global_step_20/eval_results.json",
    "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl/global_step_40/eval_results.json",
    "/nas/shared/sys2/liyizhi/folder-0630/eval_log/DLC_naive_128/Subsetreward_entropy_3B_BoN4_no_entropy_with_kl/global_step_80/eval_results.json",
],
"sft":[
    "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/new_score_subset_new/scores_7-11-hour-17/saves_scores_7-11-hour-17.json",
    ]
}