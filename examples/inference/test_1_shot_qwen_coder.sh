#!/bin/bash

# NCCL Settings
export NCCL_IB_HCA=mlx5_bond_1,mlx5_bond_2,mlx5_bond_3,mlx5_bond_4
export NCCL_IB_TC=136
export NCCL_IB_SL=5
export NCCL_IB_GID_INDEX=3
export NCCL_SOCKET_IFNAME=en,eth,em,bond
export NCCL_DEBUG=INFO

# Project settings
project_name='Inference'
exp_name="${EXP_NAME:-reform_DLC_test}"

# Environment Variables
MASTER_ADDR=${MASTER_ADDR}
MASTER_PORT=${MASTER_PORT}
WORLD_SIZE=${WORLD_SIZE}  # 节点
RANK=${RANK}
GPUS_PER_NODE=8
CPUS_PER_TASK=72
MEM_PER_TASK=$((1200 * 1024 ** 3))
GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# Arrays for experiment names and global steps
ckpt_dir=("${CHECKPOINT_ROOT:-rl_checkpoints}/" "${CHECKPOINT_ROOT:-rl_checkpoints}/")

# Calculate total tasks (all pairs)
TOTAL_TASKS=${#ckpt_dir[@]}

# 其他参数
BoN=4
BATCH_SIZE=1024
PPO_MINI_BATCH_SIZE=256
TENSOR_MODEL_PARALLEL_SIZE=1

TRAIN_FILE="${TRAIN_FILE:-dataset/dataset5k_not_trained_sft/train.parquet}"
EVAL_FILE="${EVAL_FILE:-dataset/dataset5k_v3/test.parquet}"

# 激活环境
[ -n "${CONDA_INIT:-}" ] && source "$CONDA_INIT"
conda activate "${CONDA_ENV:-vericode}"
cd "${REFORM_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

# 循环处理分配给当前节点的所有模型
for ((i=0; i<TOTAL_TASKS; i++)); do
    # 使用求余运算判断是否该当前节点处理
    if [ $((i % WORLD_SIZE)) -eq $RANK ]; then
        # Calculate which exp_name and global_step to use
        
        current_ckpt_dir=${ckpt_dir[$i]}
        
        # 创建每个模型独立的输出目录
        OUTPUT_DIR="eval_logs/${exp_name}"
        mkdir -p $OUTPUT_DIR
        
        echo "Node ${RANK} processing task $((i+1)): exp_name=${current_exp_name}, global_step=${current_global_step}"
        
        # 运行推理
        python -m verl.inference.plot_sft \
            data.path=$EVAL_FILE \
            data.filter_overlong_prompts=True \
            data.truncation='error' \
            data.prompt_type=sft \
            data.num_cpu=8 \
            model.path=$MODEL_PATH \
            rollout.temperature=1.2 \
            rollout.top_k=50  \
            rollout.top_p=0.95 \
            rollout.max_prompt_length=2048 \
            rollout.max_response_length=2048 \
            trainer.project_name="${project_name}" \
            trainer.experiment_name="qwen_coder_shot_1" \
            trainer.n_gpus_per_node=${GPUS_PER_NODE} \
            trainer.nnodes=1 \
            trainer.save_output=True \
            trainer.output_dir=$OUTPUT_DIR \
            parallel_processing.tensor_parallel_size=2 \
            plot.shot_numbers=[4] \
            plot.base_paths=["${current_ckpt_dir}"] \
            | tee qwen_coder_shot_1.log
        
        wait
        
        echo "Node ${RANK} completed task $((i+1)): exp_name=${current_exp_name}, global_step=${current_global_step}"
    fi
done

echo "Node ${RANK} completed all assigned models"