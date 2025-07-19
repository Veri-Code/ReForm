from vllm import LLM, SamplingParams
import time
from concurrent.futures import ThreadPoolExecutor
import os
import torch
import re
# from ray.train import load_checkpoint
from transformers import AutoTokenizer, AutoModelForCausalLM, AutoProcessor


os.environ["VLLM_WORKER_MULTIPROC_METHOD"] = "spawn"

def retrieve_text(output):
    # Potentially expensive call
    return output.outputs[0].text

def extract_text(output):
    return output.outputs[0].text


class BaseModel:
    def __init__(self):
        pass

    def obtain_answer(self, *args, **kwargs):
        pass

class QwenModel(BaseModel):
    def __init__(self, model_name_or_path, tensor_parallel_size=1, gpu_memory_utilization=0.8, **kwargs):
        super().__init__()
        # Initialize vLLM model with additional parameters
        vllm_kwargs = {
            'tensor_parallel_size': tensor_parallel_size,
            'gpu_memory_utilization': gpu_memory_utilization,
            **kwargs
        }
        
        try:
            self.llm = LLM(model=model_name_or_path, **vllm_kwargs)
            tokenizer = AutoTokenizer.from_pretrained(model_name_or_path)
            os.environ["TOKENIZERS_PARALLELISM"] = "false"
            processor = AutoProcessor.from_pretrained(model_name_or_path)
            self.tokenizer = tokenizer  
            self.processor = processor
        except:
            folder_name = os.path.join(model_name_or_path, "merged_checkpoint")

            if not os.path.exists(folder_name):
                file_names = os.listdir(model_name_or_path)
                # file_name = file_names[0]

                # from the name world_size_{} extract the world_size
                
                world_size = len(file_names) // 3
                # world_size = 16
                model_state = {}
                for rank in range(world_size):  # world_size 是 16
                    model_file = os.path.join(model_name_or_path, f"model_world_size_{world_size}_rank_{rank}.pt")
                    rank_state = torch.load(model_file, weights_only=True, map_location="cpu")
                    # 将 rank 的状态合并到 model_state
                    for key in rank_state:
                        # print(key)
                        val = rank_state[key]
                        if hasattr(val, 'to_local'):
                            val = val.to_local()
                        if key in model_state:
                            model_state[key].append(val)
                        else:
                            model_state[key] = [val]
                for key in model_state:
                    model_state[key] = torch.cat(model_state[key], dim=0)


                if "0.5B" in model_name_or_path:
                    model = AutoModelForCausalLM.from_pretrained("/oss/public/user/xuxu/distilled/ckpt_opt/SKD_RKL-0.5B_14B")
                    tokenizer = AutoTokenizer.from_pretrained("/oss/public/user/xuxu/distilled/ckpt_opt/SKD_RKL-0.5B_14B")
                    processor = AutoProcessor.from_pretrained("/oss/public/user/xuxu/distilled/ckpt_opt/SKD_RKL-0.5B_14B")
                if "3B" or "3b" in model_name_or_path:
                    model = AutoModelForCausalLM.from_pretrained("/nas/shared/sys2/liyizhi/Qwen2.5-Coder-3B_5k_sft_opt")
                    tokenizer = AutoTokenizer.from_pretrained("/nas/shared/sys2/liyizhi/Qwen2.5-Coder-3B_5k_sft_opt")
                    processor = AutoProcessor.from_pretrained("/nas/shared/sys2/liyizhi/Qwen2.5-Coder-3B_5k_sft_opt")
                elif "7B" in model_name_or_path:
                    model = AutoModelForCausalLM.from_pretrained("/nas/shared/sys2/liyizhi/Qwen2.5-Coder-7B_5k_sft_opt")
                    tokenizer = AutoTokenizer.from_pretrained("/nas/shared/sys2/liyizhi/Qwen2.5-Coder-7B_5k_sft_opt")
                    processor = AutoProcessor.from_pretrained("/nas/shared/sys2/liyizhi/Qwen2.5-Coder-7B_5k_sft_opt")
                elif "14B" in model_name_or_path:
                    model = AutoModelForCausalLM.from_pretrained("/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-14B_5k_sft_opt")
                    tokenizer = AutoTokenizer.from_pretrained("/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-14B_5k_sft_opt")
                    processor = AutoProcessor.from_pretrained("/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-14B_5k_sft_opt")
                model.load_state_dict(model_state)

                model.save_pretrained(folder_name)
                tokenizer.save_pretrained(folder_name)
                processor.save_pretrained(folder_name)

            print("folder_name", folder_name)
            self.llm = LLM(model=folder_name, **vllm_kwargs)  
            tokenizer = AutoTokenizer.from_pretrained(folder_name)
            os.environ["TOKENIZERS_PARALLELISM"] = "false"
            processor = AutoProcessor.from_pretrained(folder_name)
            self.tokenizer = tokenizer  
            self.processor = processor


    def obtain_multiple_answer_multishot(self, input_text_tuples, generate_args, shot_number=3):
        seed = int(time.time()) % 1000000
        sampling_params = SamplingParams(
            temperature=generate_args.get('temperature', 0.95),
            top_p=generate_args.get('top_p', 0.7),
            top_k=generate_args.get('top_k', 50),
            max_tokens=generate_args.get('max_response_length', 4500),
            n=shot_number,  # Generate multiple outputs per input
            seed = seed,
            stop= ['<im_end>'],  # stop_token_ids = [151668]
        )

        generation_start = time.time()
        with torch.autocast(device_type='cuda', dtype=torch.bfloat16):
            outputs = self.llm.generate(input_text_tuples, sampling_params)

        # Convert outputs generator to list
        outputs = list(outputs)
        print(f"Generation preparation time: {time.time() - generation_start:.2f} seconds")

        retrieval_start = time.time()

        all_outputs = []
        for output in outputs:
            # for item in output.outputs:
            #     print("Debug: item.text", item.text)
            shots = [item.text for item in output.outputs]  # Correctly retrieve multiple samples per prompt
            all_outputs.append(shots)

        print(f"Retrieval time: {time.time() - retrieval_start:.2f} seconds")

        return all_outputs
