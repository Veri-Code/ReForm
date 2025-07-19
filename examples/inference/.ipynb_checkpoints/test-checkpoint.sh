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
exp_name='fengdi_plot_scores_vs_shots_test'
export WANDB_API_KEY=2ca4169be643483a1a1694f52e6e0a90a594a021

# Environment Variables
MASTER_ADDR=${MASTER_ADDR}
MASTER_PORT=${MASTER_PORT}
WORLD_SIZE=${WORLD_SIZE:-30}
RANK=${RANK}
GPUS_PER_NODE=8
CPUS_PER_TASK=60
MEM_PER_TASK=$((1200 * 1024 ** 3))
GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# Model list - 定义30个模型路径
MODELS=(
    "/oss/public/user/chefengdi/ckpts/model_1"
    "/oss/public/user/chefengdi/ckpts/model_2"
)

# 根据RANK选择对应的模型
MODEL_PATH=${MODELS[$RANK]}

# 其他参数
BoN=4
BATCH_SIZE=1024
PPO_MINI_BATCH_SIZE=256
TENSOR_MODEL_PARALLEL_SIZE=1

TRAIN_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/train.parquet"
EVAL_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_v3/test.parquet"

# 激活环境
source /nas/shared/sys2/liyizhi/conda_init.sh
conda activate /nas/shared/sys2/chefengdi/conda/verl_clone
cd /nas/shared/sys2/liyizhi/fengdi_tinyzero

# 创建每个node独立的输出目录
OUTPUT_DIR="/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/node_${RANK}"
mkdir -p $OUTPUT_DIR

# 运行推理，每个node处理一个模型
python -m verl.inference.plot \
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
    trainer.experiment_name="${exp_name}_node_${RANK}" \
    trainer.n_gpus_per_node=${GPUS_PER_NODE} \
    trainer.nnodes=1 \
    trainer.save_output=True \
    trainer.output_dir=$OUTPUT_DIR \
    parallel_processing.tensor_parallel_size=4 \
    plot.base_paths=["/oss/public/user/chefengdi/ckpts/"] \
    plot.exp_names=["3B_naive_prevent_hacking_rollout_32 "] \
    plot.global_steps=[310] \
    plot.shot_numbers=[128] \
    | tee ${exp_name}_node_${RANK}.log

echo "Node ${RANK} completed processing model: ${MODEL_PATH}"