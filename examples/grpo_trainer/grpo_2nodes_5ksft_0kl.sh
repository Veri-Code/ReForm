# set -x

export NCCL_IB_HCA=mlx5_bond_1,mlx5_bond_2,mlx5_bond_3,mlx5_bond_4
export NCCL_IB_TC=136
export NCCL_IB_SL=5
export NCCL_IB_GID_INDEX=3
export NCCL_SOCKET_IFNAME=en,eth,em,bond
export NCCL_DEBUG=INFO

project_name='Test'
exp_name='DLC_2nodes_5ksft_0kl2'
export WANDB_API_KEY=2ca4169be643483a1a1694f52e6e0a90a594a021

# Environment Variables
MASTER_ADDR=${MASTER_ADDR}
MASTER_PORT=${MASTER_PORT}
WORLD_SIZE=${WORLD_SIZE}
RANK=${RANK}
GPUS_PER_NODE=8 # Depend on your need
CPUS_PER_TASK=60 # Depend on your need
MEM_PER_TASK=$((1200 * 1024 ** 3)) # Depend on your need
GPU_TOTAL=$((GPUS_PER_NODE * WORLD_SIZE))

# Ray head node port
RAY_PORT=6379
ip_head=${MASTER_ADDR}:${RAY_PORT}
RAY_CLUSTER_ADDRESS=${ip_head}
BoN=4
BATCH_SIZE=512  # Changed from 1024 to 1008 to make it divisible by 24 (GPU_TOTAL)
PPO_MINI_BATCH_SIZE=256  # Changed from 256 to 168 to make it divisible by 24 and 1008
TENSOR_MODEL_PARALLEL_SIZE=4


##################################################################################################################
# Check if BoN * BATCH_SIZE is divisible by GPU_TOTAL
total_samples=$((BoN * BATCH_SIZE))
if [ $((total_samples % GPU_TOTAL)) -ne 0 ]; then
    echo "Error: BoN * BATCH_SIZE (${total_samples}) must be divisible by GPU_TOTAL (${GPU_TOTAL})"
    echo "Current values:"
    echo "BoN = ${BoN}"
    echo "BATCH_SIZE = ${BATCH_SIZE}"
    echo "GPU_TOTAL = ${GPU_TOTAL}"
    echo "Please adjust BoN or BATCH_SIZE to make them divisible"
    exit 1
fi

# Check if PPO_MINI_BATCH_SIZE is divisible by GPU_TOTAL
if [ $((PPO_MINI_BATCH_SIZE % GPU_TOTAL)) -ne 0 ]; then
    echo "Error: PPO_MINI_BATCH_SIZE (${PPO_MINI_BATCH_SIZE}) must be divisible by GPU_TOTAL (${GPU_TOTAL})"
    exit 1
fi

# Check if BATCH_SIZE is divisible by PPO_MINI_BATCH_SIZE
if [ $((BATCH_SIZE % PPO_MINI_BATCH_SIZE)) -ne 0 ]; then
    echo "Error: BATCH_SIZE (${BATCH_SIZE}) must be divisible by PPO_MINI_BATCH_SIZE (${PPO_MINI_BATCH_SIZE})"
    exit 1
fi

# Check if tensor_model_parallel_size is divisible by GPU_TOTAL
if [ $((GPU_TOTAL % TENSOR_MODEL_PARALLEL_SIZE)) -ne 0 ]; then
    echo "Error: GPU_TOTAL (${GPU_TOTAL}) must be divisible by TENSOR_MODEL_PARALLEL_SIZE (${TENSOR_MODEL_PARALLEL_SIZE})"
    exit 1
fi

# Check if BoN is divisible by GPU_TOTAL
if [ $((GPU_TOTAL % BoN )) -ne 0 ]; then
    echo "Error: GPU_TOTAL (${GPU_TOTAL}) must be divisible by BoN (${BoN})"
    exit 1
fi

source /nas/shared/sys2/liyizhi/conda_init.sh
conda activate verl_public
cd /nas/shared/sys2/liyizhi/test_tinyzero

# Training Config
MODEL_PATH="/oss/public/user/xuxu/saves/Qwen2.5-Coder-7B_5k_sft_opt" # Adjust if you want to use the 7B model or another
TRAIN_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained/train.parquet"
EVAL_FILE="/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained/test.parquet"


##################################################################################################################
if [ "$RANK" -eq 0 ]; then
    # Head Node (RANK 0)

    # Clean undesirable Ray processes
    echo "Node ${RANK}: Cleaning up any existing Ray processes..."
    ray stop
    sleep 2
    
    # Kill any remaining ray processes
    pkill -f ray
    sleep 2
    
    # Clean up temporary files
    rm -rf /tmp/ray/*
    
    # Check if port is available using pure bash
    check_port() {
        local port=$1
        (echo >/dev/tcp/127.0.0.1/$port) >/dev/null 2>&1 && return 0 || return 1
    }
    
    if check_port ${RAY_PORT}; then
        echo "Port ${RAY_PORT} is in use. Waiting for it to be released..."
        sleep 10
        if check_port ${RAY_PORT}; then
            echo "Port ${RAY_PORT} is still in use. Please check manually."
            exit 1
        fi
    fi

    echo "Node ${RANK}: Starting Ray HEAD at ${MASTER_ADDR}"
    # Use `docker exec` to run ray start inside the container 
    ray start --head \
    --node-ip-address="${MASTER_ADDR}" \
    --port=${RAY_PORT} \
    --dashboard-port=8266 \
    --num-cpus "${CPUS_PER_TASK}" \
    --num-gpus "${GPUS_PER_NODE}" \
    --memory="${MEM_PER_TASK}" \
    --dashboard-host=0.0.0.0
    # --block & # Run in background, `--block` seems necessary for some Ray versions to wait for init? Testing needed. If causes issues, remove --block.
    # Allow head node time to start
    echo "Node ${RANK}: Waiting for Ray head to initialize..."

    sleep 20 # Increased sleep

    # Optional: Add check for Ray head status
    # docker exec "${CONTAINER_NAME}" ray status

else
    # Worker Nodes (RANK > 0)
    echo "Node ${RANK}: Waiting for Ray head to be ready at ${ip_head}..."
    # Simple sleep to wait for the head node. Robustness could be improved.
    sleep 30 # Workers wait longer

    echo "Node ${RANK}: Starting Ray WORKER, connecting to ${ip_head}"
    ray start --address "$ip_head" \
    --num-cpus "${CPUS_PER_TASK}" \
    --num-gpus "${GPUS_PER_NODE}" \
    --memory="${MEM_PER_TASK}"
    # --block & # Run in background
    echo "Node ${RANK}: Ray worker initiated connection."
    sleep 20 # Allow worker time to connect

fi


##################################################################################################################
if [ "$RANK" -eq 0 ]; then
    echo "Node ${RANK}: Waiting for ${WORLD_SIZE} nodes to join the Ray cluster..."
    check_cluster_ready() {
        # Get cluster status
        cluster_status=$(ray status --address="$ip_head" 2>&1)
        if [ $? -ne 0 ]; then
            echo "Node ${RANK}: Ray head is not responsive"
            return 1
        fi

        # Print current status for visibility
        echo "Current Ray cluster status:"
        echo "$cluster_status"
        
        # Count active nodes
        worker_count=$(echo "$cluster_status" | sed -n '/Active:/,/Pending:/p' | grep "node_" | wc -l)
        expected_nodes=$((WORLD_SIZE))
        
        echo "Found ${worker_count} nodes (expecting ${expected_nodes})"
        
        # Check if we have enough nodes
        if [ "$worker_count" -lt "$expected_nodes" ]; then
            return 1
        fi
        
        return 0
    }
    
    # Phase 1: Wait for cluster to be ready
    while true; do
        if check_cluster_ready; then
            echo "Node ${RANK}: Ray cluster is ready with all nodes connected!"
            break
        fi
        echo "Node ${RANK}: Waiting for all nodes to connect..."
        sleep 5
    done
    
    # Phase 2: Wait for all GPUs to be available
    expected_total_gpus=$((WORLD_SIZE * GPUS_PER_NODE))
    echo "Expecting total ${expected_total_gpus} GPUs (${WORLD_SIZE} nodes * ${GPUS_PER_NODE} GPUs per node)"
    
    # Wait for Ray to recognize all GPUs
    while true; do
        cluster_status=$(ray status --address="$ip_head" 2>&1)
        total_gpus=$(echo "$cluster_status" | grep -o "[0-9.]\+/[0-9.]\+ GPU" | awk -F'/' '{print $2}' | awk '{print $1}')
        
        if [ ! -z "$total_gpus" ]; then
            total_gpus_int=${total_gpus%.*}
            echo "Current available GPUs: ${total_gpus_int} / ${expected_total_gpus}"
            
            if [ "$total_gpus_int" -eq "$expected_total_gpus" ]; then
                echo "Node ${RANK}: All ${expected_total_gpus} GPUs are now available!"
                break
            fi
        else
            echo "Node ${RANK}: Waiting for GPU information..."
        fi
        
        sleep 5
    done
    
    echo "Node ${RANK}: === Ray cluster initialization completed ==="
   
   
##################################################################################################################
    # --- Data Preprocessing & Model Download (Run only on RANK 0) ---
    echo "Node ${RANK}: Preparing RL Data..."
    echo "Training file: $TRAIN_FILE"
    echo "Evaluation file: $EVAL_FILE"

    echo "Node ${RANK}: Preparing RL Actor Model..."
    # Define the base model path for downloading/testing
    echo $MODEL_PATH


    echo "Node ${RANK}: == Data and model loading Done =="
    echo "Node ${RANK}: Preparing for training..."

    # --- Training Launch (Run only on RANK 0) ---
    echo "Node ${RANK}: Starting VERL RL training..."
    
##################################################################################################################
    # Note: We are NOT using torchrun here. We run the command on Rank 0,
    # and the verl.trainer.main_ppo script uses the Ray cluster we set up.
    
    # - batch_size * rollout.n must be divisible by total_gpus (24)
    ray job submit --address="http://127.0.0.1:8266" \
        --working-dir=/nas/shared/sys2/liyizhi/test_tinyzero \
        --runtime-env=verl/trainer/runtime_env.yaml \
        -- \
        python3 -m verl.trainer.main_ppo \
            algorithm.adv_estimator=grpo \
            data.train_files=$TRAIN_FILE \
            data.val_files=$EVAL_FILE \
            data.train_batch_size=${BATCH_SIZE} \
            data.max_prompt_length=2048 \
            data.max_response_length=2048 \
            data.filter_overlong_prompts=True \
            data.truncation='error' \
            actor_rollout_ref.model.path=$MODEL_PATH \
            actor_rollout_ref.actor.optim.lr=1e-5 \
            actor_rollout_ref.model.use_remove_padding=True \
            actor_rollout_ref.actor.ppo_mini_batch_size=${PPO_MINI_BATCH_SIZE} \
            actor_rollout_ref.actor.use_dynamic_bsz=True \
            actor_rollout_ref.actor.ppo_max_token_len_per_gpu=8000 \
            actor_rollout_ref.actor.use_kl_loss=False \
            actor_rollout_ref.actor.kl_loss_coef=0.0 \
            actor_rollout_ref.actor.kl_loss_type=low_var_kl \
            actor_rollout_ref.actor.entropy_coeff=0 \
            actor_rollout_ref.model.enable_gradient_checkpointing=True \
            actor_rollout_ref.actor.fsdp_config.param_offload=False \
            actor_rollout_ref.actor.fsdp_config.optimizer_offload=False \
            actor_rollout_ref.rollout.tensor_model_parallel_size=${TENSOR_MODEL_PARALLEL_SIZE} \
            actor_rollout_ref.rollout.name=vllm \
            actor_rollout_ref.rollout.gpu_memory_utilization=0.6 \
            actor_rollout_ref.rollout.n=${BoN} \
            actor_rollout_ref.ref.fsdp_config.param_offload=True \
            actor_rollout_ref.rollout.enforce_eager=False \
            actor_rollout_ref.rollout.free_cache_engine=False \
            algorithm.use_kl_in_reward=False \
            trainer.critic_warmup=0 \
            trainer.logger=['console','wandb'] \
            trainer.project_name="${project_name}" \
            trainer.experiment_name="${exp_name}" \
            trainer.val_before_train=True \
            trainer.n_gpus_per_node=${GPUS_PER_NODE} \
            trainer.nnodes=${WORLD_SIZE} \
            trainer.save_freq=5 \
            trainer.test_freq=1 \
            trainer.default_local_dir=/nas/shared/sys2/liyizhi/new_checkpoints/${exp_name} \
            trainer.total_epochs=20 | tee ${exp_name}.log

    echo "Node ${RANK}: Training finished."

else
    # --- Worker Nodes Wait ---
    echo "Node ${RANK}: Worker node waiting for training to complete..."
    # Workers just need to keep their Ray process alive inside the container.
    # The `tail -f /dev/null` in the `docker run` command keeps the container running.
    # The script on the worker node can technically exit here, but we'll wait indefinitely
    # to prevent the overall job orchestrator (if any) from thinking this node finished prematurely.
    # This assumes the orchestrator waits for the script on *all* nodes to exit.
    # wait # Wait for background processes like 'ray start &' if they weren't fully daemonized
    # If 'wait' returns immediately, use sleep:
    sleep infinity
    echo "Node ${RANK}: Worker finished waiting."

fi

echo "Node ${RANK}: Script execution finished."
exit 0

