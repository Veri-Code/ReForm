project_name='Inference'
exp_name='SpecRefinement-3B'
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

# export WANDB_API_KEY=5edb8fccc26de7f9c2baeb46780bcd22d0588c62
source /nas/shared/sys2/liyizhi/conda_init.sh
conda activate verl_public
cd /nas/shared/sys2/liyizhi/test_tinyzero3

MODEL_PATH="/oss/public/user/chefengdi/ckpts/${exp_name}/global_step_${global_steps}/actor"
# MODEL_PATH="/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/a2a_lemma_kept_wcompiler_cot/Qwen2.5-Coder-3B_a2a_lemma_kept_5k_wcompiler_1mid_cot_sft_new"

# Adjust if you want to use the 7B model or another
# MODEL_PATH="/root/Qwen2.5-Coder-3B_5k_sft_opt" # Adjust if you want to use the 7B model or another
TRAIN_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/train.parquet"
EVAL_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained_sft/test.parquet"
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
    trainer.output_dir=/nas/shared/sys2/chefengdi/dafny_full_log/ \
# rollout.top_k 0 for hf rollout, -1 for vllm rollout