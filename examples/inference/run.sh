project_name='Inference'
exp_name="${EXP_NAME:-SpecRefinement-3B}"
global_steps=20
WORLDSIZE=1
GPUS_PER_NODE=8 # Depend on your need
# CPUS_PER_TASK=60 # Depend on your need
# MEM_PER_TASK=$((1200 * 1024 ** 3)) # Depend on your need
# GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# Ray head node port
# RAY_PORT=6379
# ip_head=${MASTER_ADDR}:${RAY_PORT}
# RAY_CLUSTER_ADDRESS=${ip_head}
BoN=8
BATCH_SIZE=1024  # Changed from 1024 to 1008 to make it divisible by 24 (GPU_TOTAL)
PPO_MINI_BATCH_SIZE=256  # Changed from 256 to 168 to make it divisible by 24 and 1008
TENSOR_MODEL_PARALLEL_SIZE=1

[ -n "${CONDA_INIT:-}" ] && source "$CONDA_INIT"
conda activate "${CONDA_ENV:-vericode}"
cd "${REFORM_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

MODEL_PATH="${MODEL_PATH:-rl_checkpoints/${exp_name}/global_step_${global_steps}/actor}"
# MODEL_PATH="${MODEL_PATH:-sft_ckpts/sft_3B}"

# Adjust if you want to use the 7B model or another
# MODEL_PATH="${MODEL_PATH:-sft_ckpts/sft_7B}"
TRAIN_FILE="${TRAIN_FILE:-dataset/dataset5k_not_trained_sft/train.parquet}"
EVAL_FILE="${EVAL_FILE:-dataset/dataset5k_not_trained_sft/test.parquet}"
python3 -m verl.inference.eval \
    data.path=$EVAL_FILE \
    data.filter_overlong_prompts=True \
    data.truncation='error' \
    data.prompt_type=sft \
    model.path=$MODEL_PATH \
    rollout.temperature=1.0 \
    rollout.top_k=50  \
    rollout.top_p=0.7 \
    rollout.max_prompt_length=2048 \
    rollout.max_response_length=2048 \
    rollout.shot_number=1 \
    trainer.project_name="${project_name}" \
    trainer.experiment_name="${exp_name}" \
    trainer.n_gpus_per_node=${GPUS_PER_NODE} \
    trainer.nnodes=${WORLDSIZE} \
    trainer.save_output=False \
    trainer.output_dir="eval_logs/${exp_name}" \
# rollout.top_k 0 for hf rollout, -1 for vllm rollout
