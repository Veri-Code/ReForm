#!/bin/bash

export NCCL_IB_HCA=mlx5_bond_1,mlx5_bond_2,mlx5_bond_3,mlx5_bond_4
export NCCL_IB_TC=136
export NCCL_IB_SL=5
export NCCL_IB_GID_INDEX=3
export NCCL_SOCKET_IFNAME=bond0
export NCCL_DEBUG=INFO

# Environment Variables
WORLD_SIZE=${WORLD_SIZE}
GPUS_PER_NODE=8 # Depend on your need
CPUS_PER_TASK=96 # Depend on your need
MEM_PER_TASK=$((1280 * 1280 ** 3)) # Depend on your need
GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# export WANDB_API_KEY=5edb8fccc26de7f9c2baeb46780bcd22d0588c62
source /nas/shared/sys2/liyizhi/conda_init.sh
conda activate /nas/shared/sys2/chefengdi/conda/verl_clone
cd /nas/shared/sys2/liyizhi/test_tinyzero3

# Adjust if you want to use the 7B model or another
MODEL_PATH="/root/Qwen2.5-Coder-3B_5k_sft_opt" # Adjust if you want to use the 7B model or another
TRAIN_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/train.parquet"
EVAL_FILE="/nas/shared/sys2/chefengdi/dafny_full_log/dafny_bench_lemma_kept_remove_240.parquet"


# Default values
TASKS_FILE="/nas/shared/sys2/chefengdi/eval_log/tasks/eval_tasks.json"
NUM_GPUS=4
BATCH_SIZE=48   # 48 is the max batch size for 4 GPUs


# Function to run a single task
run_task() {
    local task_json="$1"
    local task_id=$(echo "$task_json" | jq -r '.task_id')
    local model_path=$(echo "$task_json" | jq -r '.model_path')
    local exp_name=$(echo "$task_json" | jq -r '.exp_name')
    local step=$(echo "$task_json" | jq -r '.step')
    local prompt_type=$(echo "$task_json" | jq -r '.prompt_type')
    local max_shot=$(echo "$task_json" | jq -r '.max_shot')
    local task_output_dir=$(echo "$task_json" | jq -r '.output_dir')
    
    mkdir -p "$task_output_dir"
    
    # Create task-specific config
    local task_config="$task_output_dir/config.yaml"
    echo "$task_json" | jq -r '.config' > "$task_config"
    
    echo "Running task $task_id: $exp_name step $step"
    
    # Launch torchrun for this task
    torchrun \
        --nproc_per_node=$NUM_GPUS \
        --rdzv_id=eval_job \
        --rdzv_backend=c10d \
        --rdzv_endpoint=$MASTER_ADDR:$MASTER_PORT \
        -m verl.inference.eval \
        --config-path="$task_config" \
        model.path="$model_path" \
        rollout.shot_number="$max_shot" \
        rollout.temperature=1.2 \
        rollout.top_k=50  \
        rollout.top_p=0.95 \
        rollout.max_prompt_length=2048 \
        rollout.max_response_length=2048 \
        data.prompt_type="$prompt_type" \
        data.filter_overlong_prompts_workers=1  \
        data.dataloader_num_workers=0  \
        data.batch_size = "$BATCH_SIZE" \
        data.return_raw_chat = False \
        data.truncation = 'error' \
        data.path=$EVAL_FILE \
        data.filter_overlong_prompts=True \
        trainer.output_dir="$task_output_dir" \
        trainer.project_name="${project_name}" \
        trainer.experiment_name="${exp_name}" \
        trainer.nnodes=1 \
        trainer.save_output=True \
        parallel_processing.tensor_parallel_size="$NUM_GPUS" \
        trainer.n_gpus_per_node = "$NUM_GPUS" \
        trainer.output_dir=/nas/shared/sys2/chefengdi/eval_log/3B_bench_16shots/ \
    # Delete the task_output_dir
    rm -rf "$task_output_dir"

}

# Read tasks from JSON file and run them
jq -c '.[]' "$TASKS_FILE" | while read -r task; do
    run_task "$task"
done 