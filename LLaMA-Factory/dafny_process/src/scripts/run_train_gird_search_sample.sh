#!/bin/bash
{
# Conda Env Activation

# Custom
export WANDB_API_KEY=xxxx
export WANDB_PROJECT=xxxx

export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True

cd Path to LLaMA-Factory

model_sizes=("0.5" "1.5" "3" "7" "14" "32")
training_datasets=("dataset1 name in data/datset_info.json" "dataset2 name in data/datset_info.json")  # TODO: Replace with your actual dataset names

# Config index range (optional)
config_index_start=$1
config_index_end=$2

for size in "${model_sizes[@]}"; do
    # Set config folder for each model size
    config_folder="examples/qwen${size}B_pure_sft_grid_search"
    if [ ! -d "$config_folder" ]; then
        echo "Config folder $config_folder does not exist, skip."
        continue
    fi

    # Collect all config paths
    config_path_list=()
    for config_path in ${config_folder}/*.yaml; do
        config_path_list+=(${config_path})
    done

    # Default: run all configs
    if [ -z "${config_index_start}" ]; then
        config_index_start=1
    fi
    if [ -z "${config_index_end}" ]; then
        config_index_end=${#config_path_list[@]}
    fi
    echo "Model size: ${size}B, running config indices: ${config_index_start} - ${config_index_end}"

    # Select configs to run
    config_path_list=(${config_path_list[@]:${config_index_start}-1:${config_index_end}-${config_index_start}+1})

    for config_path in ${config_path_list[@]}; do
        config_name=$(basename ${config_path%.yaml})
        for training_dataset in "${training_datasets[@]}"; do
            # Replace dataset field in config file
            sed -i "s/^dataset: .*/dataset: ${training_dataset}/g" ${config_path}
            output_dir=$(sed -n 's/^output_dir: //p' ${config_path} | tr -d ' ')
            echo "Checking ${output_dir}"

            if [ -e "${output_dir}/model.safetensors.index.json" ]; then
                echo "Training output found in ${output_dir}, skip training"
                continue
            else
                echo "Running: ${config_name} with dataset ${training_dataset}"
                log_path=logs/grid_search_${size}B_${config_name}_${training_dataset}.log
                FORCE_TORCHRUN=1 llamafactory-cli train ${config_path} 2>&1 | tee -a ${log_path}
            fi
        done
    done
done

exit
}