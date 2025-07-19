#!/bin/bash
{
    source /nas/shared/sys2/liyizhi/conda_init.sh
    conda activate llamafactory

    export PATH="/nas/shared/sys2/liyizhi/miniconda3/envs/llamafactory/bin:$PATH"
    
    cd /nas/shared/sys2/liyizhi/LLaMA-Factory


    
    # inference_dataset=dafny_small_dev # must explicitly equal to dataset name in the dataset_info.json

    for inference_dataset in a2a_lemma_kept_vanilla_cot_dev; do

        output_folder=/nas/shared/sys2/chefengdi/inference_outputs/no_parse_error/${inference_dataset}
        mkdir -p $output_folder

        for model_size in "0.5" "3" "7" ; do
            if [ "$model_size" = "0.5" ]; then
                gpu_id=1
            elif [ "$model_size" = "3" ]; then
                gpu_id=2
            else
                gpu_id=3,4
            fi
            
            for instruc in "1" "2"; do
                CUDA_VISIBLE_DEVICES=${gpu_id} python scripts/vllm_infer.py --model_name_or_path saves/a2a_lemma_kept_alcot/Qwen2.5-Coder-${model_size}B_a2a_lemma_kept_alcot_remove_parsererr_train_sft \
                    --dataset ${inference_dataset} --template qwen --cutoff_len 4096 \
                    --save_name $output_folder/Qwen2.5-Coder-${model_size}B_sft.jsonl &
            done
        done
#         CUDA_VISIBLE_DEVICES=4,5 python scripts/vllm_infer.py --model_name_or_path saves/Qwen2.5-Coder-7B_dafny_v1_vanilla_partial_remove_sft \
#             --dataset ${inference_dataset} --template qwen --cutoff_len 4096 \
#             --save_name $output_folder/Qwen2.5-Coder-7B_dafny_v1_vanilla_partial_remove_sft.jsonl &

#         CUDA_VISIBLE_DEVICES=6,7 python scripts/vllm_infer.py --model_name_or_path saves/Qwen2.5-Coder-14B_dafny_v1_vanilla_partial_remove_sft \
#             --dataset ${inference_dataset} --template qwen --cutoff_len 4096 \
#             --save_name $output_folder/Qwen2.5-Coder-14B_dafny_v1_vanilla_partial_remove_sft.jsonl &

        wait

        sleep 3
        
        # python scripts/vllm_infer.py --model_name_or_path saves/Qwen2.5-Coder-32B_dafny_v1_vanilla_partial_remove_sft \
        #    --dataset ${inference_dataset} --template qwen --cutoff_len 4096 \
        #    --save_name $output_folder/Qwen2.5-Coder-32B_dafny_v1_vanilla_partial_remove_sft.jsonl

    done
    exit
}