exp_name='SpecRefinement-3B'
global_steps=20

# all folders
# model_path = ["/oss/public/user/xuxu/distilled/ckpt_opt/SKD_RKL-0.5B_14B",
# "/oss/public/user/xuxu/saves/Qwen2.5-Coder-1.5B_5k_sft_opt",
# "/oss/public/user/xuxu/saves/Qwen2.5-Coder-3B_5k_sft_opt",
# "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt",
# "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt",
# "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt",
# "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/a2a_lemma_kept_cot/Qwen2.5-Coder-3B_a2a_lemma_kept_cot_in1_sft",
# ]

# local_path = ["/oss/public/user/yanch/ckpts/xin_grpo_05B_0508_Bo8_reward_subgt_hacking_check",
# "/oss/public/user/yanch/ckpts/xin_grpo_1.5B_0506_Bo8_reward_subgt_hacking_check",
# "/oss/public/user/yanch/ckpts/xin_grpo_3B_0508_Bo8_reward_subgt_hacking_check",
# "/oss/public/user/chefengdi/ckpts/SpecRefinement-3B",
# "/oss/public/user/chefengdi/ckpts/SpecRefinement-3B-requires",
# "/oss/public/user/chefengdi/ckpts/grpo_8nodes_5ksft_3B_spec_refine_one_score-ensures_fixed",
# "/oss/public/user/chefengdi/ckpts/grpo_8nodes_3kins1_3B_cot_only_parse-ensures_fixed",
# ]

# steps =[20,40,60,80]

python ../verl_public/scripts/model_merger.py \
  --backend fsdp \
  --hf_model_path /nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt \
  --local_dir /oss/public/user/chefengdi/ckpts/${exp_name}/global_step_${global_steps}/actor \
  --target_dir /oss/public/user/chefengdi/ckpts/${exp_name}/global_step_${global_steps}/actor/huggingface
