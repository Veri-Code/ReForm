project_name='Inference'
exp_name='fengdi_plot_scores_vs_shots'
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

# export WANDB_API_KEY=5edb8fccc26de7f9c2baeb46780bcd22d0588c62
source /nas/shared/sys2/liyizhi/conda_init.sh
conda activate /nas/shared/sys2/chefengdi/conda/verl_clone
cd /nas/shared/sys2/liyizhi/fengdi_tinyzero

# Adjust if you want to use the 7B model or another
# MODEL_PATH="/root/Qwen2.5-Coder-3B_5k_sft_opt" # Adjust if you want to use the 7B model or another
TRAIN_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/train.parquet"
# EVAL_FILE="/nas/shared/sys2/chefengdi/dafny_full_log/sft_test_240.parquet"
EVAL_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_v3/test.parquet"
# torchrun \
# --nnodes=$WORLD_SIZE \
# --nproc_per_node=$GPUS_PER_NODE \
# --rdzv_id=eval_job \
# --rdzv_backend=c10d \
# --rdzv_endpoint=$MASTER_ADDR:$MASTER_PORT \
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
    trainer.experiment_name="${exp_name}" \
    trainer.n_gpus_per_node=${GPUS_PER_NODE} \
    trainer.nnodes=${WORLDSIZE} \
    trainer.save_output=True \
    trainer.output_dir=/nas/shared/sys2/chefengdi/eval_log/DLC_test/ \
    parallel_processing.tensor_parallel_size=4 \
    plot.base_paths=["/oss/public/user/chefengdi/ckpts/"] \
    plot.exp_names=["3B_naive_prevent_hacking_rollout_32 "] \
    plot.global_steps=[20] \
    plot.shot_numbers=[128] \
    | tee ${exp_name}.log