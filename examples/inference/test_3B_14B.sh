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
exp_name='fengdi_DLC_test'
# export WANDB_API_KEY=2ca4169be643483a1a1694f52e6e0a90a594a021

# Environment Variables
MASTER_ADDR=${MASTER_ADDR}
MASTER_PORT=${MASTER_PORT}
WORLD_SIZE=${WORLD_SIZE}  # 节点
RANK=${RANK}
GPUS_PER_NODE=8
CPUS_PER_TASK=64
MEM_PER_TASK=$((1200 * 1024 ** 3))
GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# Arrays for experiment names and global steps
# ckpt_dir=("/oss/public/user/chefengdi/ckpts" "/oss/public/user/chefengdi/ckpts" "/oss/public/user/chefengdi/ckpts")

ckpt_dir=("/oss/public/user/yanch/ckpts/" "/oss/public/user/chefengdi/ckpts")
exp_names=("Report_0715_naive_reward_3B" "3B_BoN4_subset")
global_steps=(20 40 80 160)


# Calculate total tasks (all pairs)
TOTAL_TASKS=$((${#exp_names[@]} * ${#global_steps[@]}))

# 其他参数
BoN=4
BATCH_SIZE=1024
PPO_MINI_BATCH_SIZE=256
TENSOR_MODEL_PARALLEL_SIZE=1

TRAIN_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/train.parquet"
EVAL_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_v3/test.parquet"
# EVAL_FILE="/nas/shared/sys2/chefengdi/dafny_full_log/dafny_bench_lemma_kept_remove_240.parquet"

# 激活环境
source /nas/shared/sys2/liyizhi/conda_init.sh
conda activate /nas/shared/sys2/chefengdi/conda/verl_clone
cd /nas/shared/sys2/liyizhi/fengdi_tinyzero

# 循环处理分配给当前节点的所有模型
for ((i=0; i<TOTAL_TASKS; i++)); do
    # 使用求余运算判断是否该当前节点处理
    if [ $((i % WORLD_SIZE)) -eq $RANK ]; then
        # Calculate which exp_name and global_step to use
        exp_idx=$((i / ${#global_steps[@]}))
        step_idx=$((i % ${#global_steps[@]}))
        
        current_exp_name=${exp_names[$exp_idx]}
        current_global_step=${global_steps[$step_idx]}
        current_ckpt_dir=${ckpt_dir[$exp_idx]}
        
        # 创建每个模型独立的输出目录
        OUTPUT_DIR="/nas/shared/sys2/chefengdi/report_shots/"
        mkdir -p $OUTPUT_DIR
        
        echo "Node ${RANK} processing task $((i+1)): exp_name=${current_exp_name}, global_step=${current_global_step}"
        
        # 运行推理
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
            trainer.experiment_name="${exp_name}_node_${RANK}_model_$((i+1))" \
            trainer.n_gpus_per_node=${GPUS_PER_NODE} \
            trainer.nnodes=1 \
            trainer.save_output=True \
            trainer.output_dir=$OUTPUT_DIR \
            parallel_processing.tensor_parallel_size=8 \
            plot.base_paths=["${current_ckpt_dir}"] \
            plot.exp_names=["${current_exp_name}"] \
            plot.global_steps=[${current_global_step}] \
            plot.shot_numbers=[128] \
            | tee ${current_exp_name}_node_${RANK}_step_${current_global_step}.log
        
        wait
        
        echo "Node ${RANK} completed task $((i+1)): exp_name=${current_exp_name}, global_step=${current_global_step}"
    fi
done

echo "Node ${RANK} completed all assigned models"