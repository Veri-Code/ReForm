project_name='Inference'
exp_name="${EXP_NAME:-reform_plot_scores_vs_shots}"
WORLD_SIZE=1
GPUS_PER_NODE=8 # Depend on your need
# CPUS_PER_TASK=60 # Depend on your need
# MEM_PER_TASK=$((1200 * 1024 ** 3)) # Depend on your need
# GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# Ray head node port
# RAY_PORT=6379
# ip_head=${MASTER_ADDR}:${RAY_PORT}
# RAY_CLUSTER_ADDRESS=${ip_head}
BoN=4
BATCH_SIZE=1024  # Changed from 1024 to 1008 to make it divisible by 24 (GPU_TOTAL)
PPO_MINI_BATCH_SIZE=256  # Changed from 256 to 168 to make it divisible by 24 and 1008
TENSOR_MODEL_PARALLEL_SIZE=1
MASTER_ADDR=${MASTER_ADDR:-"127.0.0.1"}
MASTER_PORT=${MASTER_PORT:-"29500"}
WORLD_SIZE=${WORLD_SIZE:-"1"}
RANK=${RANK:-"0"}

[ -n "${CONDA_INIT:-}" ] && source "$CONDA_INIT"
conda activate "${CONDA_ENV:-vericode}"
cd "${REFORM_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

# Adjust if you want to use the 7B model or another
MODEL_PATH="${MODEL_PATH:-sft_ckpts/Qwen2.5-Coder-3B_5k_sft_opt}"
TRAIN_FILE="${TRAIN_FILE:-dataset/dataset5k_not_trained_sft/train.parquet}"
EVAL_FILE="${EVAL_FILE:-dataset/dafny_bench_lemma_kept_remove_240.parquet}"
# torchrun \
# --nnodes=$WORLD_SIZE \
# --nproc_per_node=$GPUS_PER_NODE \
# --rdzv_id=eval_job \
# --rdzv_backend=c10d \
# --rdzv_endpoint=$MASTER_ADDR:$MASTER_PORT \
 python -m verl.inference.generate_tasks \
    data.path=$EVAL_FILE \
    data.filter_overlong_prompts=True \
    data.truncation='error' \
    data.prompt_type=sft \
    model.path=$MODEL_PATH \
    rollout.temperature=1.2 \
    rollout.top_k=50  \
    rollout.top_p=0.95 \
    rollout.max_prompt_length=2048 \
    rollout.max_response_length=2048 \
    rollout.shot_number=1 \
    trainer.project_name="${project_name}" \
    trainer.experiment_name="${exp_name}" \
    trainer.n_gpus_per_node=${GPUS_PER_NODE} \
    trainer.nnodes=${WORLD_SIZE} \
    trainer.save_output=True \
    trainer.output_dir="eval_logs/${exp_name}" \
    parallel_processing.tensor_parallel_size=4 \
    plot.base_paths=["${CHECKPOINT_ROOT:-rl_checkpoints}/","rl_checkpoints/","rl_checkpoints/","rl_checkpoints/","rl_checkpoints/"] \
    plot.exp_names=["DLC_4nodes_3B_reward_naive_0609_v5","reform_grpo_8nodes_5ksft_3B_spec_refine_fixed_no_hacking_v3_0530_11am","reform_grpo_5ksft_3B_specRefine_prevent_hacking_v3_0005kl_0615_9pm","reform_grpo_5ksft_3B_formal_cot_spec_prevent_hacking_v3_0618_9pm","reform_grpo_5ksft_3B_prevent_hacking_v3_0618_9pm"] \
    plot.global_steps=[20,40,60,80] \
    plot.shot_numbers=[16] \
