# Veri-Code

Specification Generation Framework for Language Models using SFT (Supervised Fine-Tuning) and RL (Reinforcement Learning) approaches ([Homepage](https://bruno686.github.io/ReForm/)).


This repository build on top of [LLaMA-Factory](https://github.com/hiyouga/LLaMA-Factory) and [Verl](https://github.com/volcengine/verl).

You can find our homepage

## Table of Contents
- [Installation](#installation)
- [Supervised Fine-Tuning (SFT)](#supervised-fine-tuning-sft)
- [Reinforcement Learning (RL)](#reinforcement-learning-rl)

## Installation

```bash
conda create -n vericode python=3.10
conda activate vericode
pip install torch==2.6.0
wget https://github.com/Dao-AILab/flash-attention/releases/download/v2.7.4.post1/flash_attn-2.7.4.post1+cu12torch2.6cxx11abiFALSE-cp310-cp310-linux_x86_64.whl
pip install flash_attn-2.7.4.post1+cu12torch2.6cxx11abiFALSE-cp310-cp310-linux_x86_64.whl
pip install -r requirements.txt
```

## Download Data and Model

You can download the data and model from https://huggingface.co/Veri-Code.


## Supervised Fine-Tuning (SFT)

<!-- ### Checkpoints
Provide SFT checkpoints directly now

put these checkpoints in the directory: (ckpt)

### Data Format
SFT training data should follow this JSON format:
```json
[
    {
        "system": "",
        "instruction": "[Main prompt] Given an xx input, generate xxx output. <think> <answer>",
        "input": "Specific question (unique for each data point)",
        "output": "Ground truth"
    }
]
```

```bash
# copied from chatml template
register_template(
    name="qwen",
    format_user=StringFormatter(slots=["<|im_start|>user\n{{content}}<|im_end|>\n<|im_start|>assistant\n"]),
    format_assistant=StringFormatter(slots=["{{content}}<|im_end|>\n"]),
    format_system=StringFormatter(slots=["<|im_start|>system\n{{content}}<|im_end|>\n"]),
    format_function=FunctionFormatter(slots=["{{content}}<|im_end|>\n"], tool_format="qwen"),
    format_observation=StringFormatter(
        slots=["<|im_start|>user\n<tool_response>\n{{content}}\n</tool_response><|im_end|>\n<|im_start|>assistant\n"]
    ),
    format_tools=ToolFormatter(tool_format="qwen"),
    default_system="You are a helpful assistant.",
    stop_words=["<|im_end|>"],
)

```

Example dataset:
```bash
/nas/shared/sys2/chefengdi/dafny_data/opt_3419_vanilla_lemma_kept_remove_assume_change_train_formalcot_remove_parseerror_250516.json
``` -->

### Training
<!-- For SFT training, please contact xuxu for assistance.

### Inference
1. Example inference script:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/examples/inference/sft_inference.sh
```

2. Place your inference dataset in:
```bash
/nas/shared/sys2/liyizhi/LLaMA-Factory/data/dataset_info.json
``` -->

## Reinforcement Learning (RL)

### Training

If you want to train with RL, please first get SFT models ready, checkpoints can be downloaded from https://huggingface.co/Veri-Code/sft_0.5B and please change the `MODEL_PATH` in `train.sh` to your SFT model path.


The Python2Dafny Data are prepared in this repository: `dataset/train.parquet` and `dataset/test.parquet`.
You can directly use them or prepare your own dataset using `src/data_preprocess.py`.

#### Single Node

```bash
bash train.sh
```

#### Multiple Nodes
```bash
bash train_multi_node.sh
```


### Evaluation
You can download our RL-pretrained model at: https://huggingface.co/Veri-Code/14B-RL-entropy

To evaluate the model, change the folder names in the file "src/evaluation.py"


```bash
python src/evaluation.py --workers 96 --folder_name logs/YOUR_LOG_DIR
```

Then you will get some json files containing the scores

You may use 
```bash
python src/plot.py --file_list eval_logs/YOUR_SCORE_JSON_FILES
```
to plot the scores


<!-- 1. Example DLC environment setup:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/examples/grpo_trainer/grpo_8nodes_2kins1_3B_cot_with_format.sh
```

2. Prompt templates for training can be modified in:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/verl/trainer/ppo/prompt_templates.py
```

- To modify prompts during inference or training, change the `prompt_type` keywords in the arguments

3. How to parse inputs and llm_outputs to call functions to compute rewards?

- The `prepare_llm_output()` function in the RL inference file demonstrates:
  1. How to parse inputs (typically starting with empty tokens)
  2. How to combine inputs and llm_outputs for reward function calls

### Inference
1. Main inference script:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/verl/inference/eval.py
```

2. Example inference configuration:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/examples/inference/run.sh
```

3. Prompt templates for inference can be modified in:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/verl/inference/llm_inference.py
```
- To modify prompts during inference or training, change the `prompt_type` keywords in the arguments
- Modified files are stored at 
```bash
/root/.cache/verl/rlhf/modified_prompts/
```

### Checkpoints
Load checkpoints using the utilities in:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/verl/inference/models.py
```

The process involves:
1. Loading a Qwen base model
2. Loading our safetensors using `load_state_dict()`

### Visualization
Generate plots using:
```bash
/nas/shared/sys2/liyizhi/test_tinyzero3/verl/inference/plot.py
``` -->
