exp_name="${EXP_NAME:-SpecRefinement-3B}"
global_steps=20

# all folders
# model_path = ["sft_ckpts/distilled/ckpt_opt/SKD_RKL-0.5B_14B",
# "sft_ckpts/saves/Qwen2.5-Coder-1.5B_5k_sft_opt",
# "sft_ckpts/saves/Qwen2.5-Coder-3B_5k_sft_opt",
# "sft_ckpts/Qwen2.5-Coder-3B_5k_sft_opt",
# "sft_ckpts/Qwen2.5-Coder-3B_5k_sft_opt",
# "sft_ckpts/Qwen2.5-Coder-3B_5k_sft_opt",
# "sft_ckpts/a2a_lemma_kept_cot/Qwen2.5-Coder-3B_a2a_lemma_kept_cot_in1_sft",
# ]

# local_path = ["rl_checkpoints/xin_grpo_05B_0508_Bo8_reward_subgt_hacking_check",
# "rl_checkpoints/xin_grpo_1.5B_0506_Bo8_reward_subgt_hacking_check",
# "rl_checkpoints/xin_grpo_3B_0508_Bo8_reward_subgt_hacking_check",
# "rl_checkpoints/SpecRefinement-3B",
# "rl_checkpoints/SpecRefinement-3B-requires",
# "rl_checkpoints/grpo_8nodes_5ksft_3B_spec_refine_one_score-ensures_fixed",
# "rl_checkpoints/grpo_8nodes_3kins1_3B_cot_only_parse-ensures_fixed",
# ]

# steps =[20,40,60,80]

python ../verl_public/scripts/model_merger.py \
  --backend fsdp \
  --hf_model_path sft_ckpts/Qwen2.5-Coder-3B_5k_sft_opt \
  --local_dir rl_checkpoints/${exp_name}/global_step_${global_steps}/actor \
  --target_dir rl_checkpoints/${exp_name}/global_step_${global_steps}/actor/huggingface
