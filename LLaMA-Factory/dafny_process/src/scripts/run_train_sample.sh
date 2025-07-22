#!/bin/bash
{
# Conda Env Activation

# Custom
export WANDB_API_KEY=xxxx
export WANDB_PROJECT=xxxx

export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True

cd Path to LLaMA-Factory

# Custom
config_dir=examples/train_full_opt
    
for model_size in "0.5" "1.5" "3" "7" "14" "32"; do
    # Custom
    for training_dataset in "dataset name in data/datset_info.json"; do
        config_path=${config_dir}/qwen25code${model_size}B_full_sft.yaml
        log_path=logs/qwen25code${model_size}B_full_sft_x.log
        
        sed -i "s/^dataset: .*/dataset: ${training_dataset}/g" ${config_path}
        #Custom
        sed -i "s/^output_dir: .*/output_dir: saves\/Qwen2.5-Coder-${model_size}B_${training_dataset}_sft/g" ${config_path}
        
        FORCE_TORCHRUN=1 llamafactory-cli train ${config_path} 2>&1 | tee -a  ${log_path}
    done
done

exit
}