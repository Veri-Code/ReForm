# Veri-Code

A framework for code to specification generation using large language models, based on Supervised Fine-Tuning (SFT) and Reinforcement Learning (RL).

## ToDo
- [ ] Add SFT dataset, training and evaluation scripts
- [ ] Add DafnyComp benchmark and evaluation codes for it


![Overall Pipeline](assets/pipeline.png)

## Table of Contents
- [Installation](#installation)
- [Dataset and Model](#dataset-and-model)
- [Training](#training)
- [Evaluation](#evaluation)
- [Reference](#reference)

## Installation
We recommend using conda for environment setup:

```bash
conda create -n vericode python=3.10
conda activate vericode

pip install torch==2.6.0

# Install FlashAttention (make sure your CUDA and PyTorch versions match)
wget https://github.com/Dao-AILab/flash-attention/releases/download/v2.7.4.post1/flash_attn-2.7.4.post1+cu12torch2.6cxx11abiFALSE-cp310-cp310-linux_x86_64.whl
pip install flash_attn-2.7.4.post1+cu12torch2.6cxx11abiFALSE-cp310-cp310-linux_x86_64.whl

pip install -r requirements.txt
```

## Dataset and Model
- The Python2Dafny dataset is located in the dataset/ directory.

- SFT and RL model checkpoints can be downloaded from https://huggingface.co/Veri-Code.

Available checkpoints:

- SFT : sft_0.5B, sft_1.5B, sft_3B, sft_7B, sft_14B

- RL fine-tuned model: 14B-RL-entropy

You can also prepare your own dataset using `src/data_preprocess.py`.


## Training

To train using reinforcement learning (RL), you must first obtain a supervised fine-tuned (SFT) model. Download a checkpoint (e.g., sft_0.5B) and set MODEL_PATH in train.sh accordingly.

The dataset used for training and evaluation is Python2Dafny by default.

### Single-node training

```bash
bash train.sh
```

### Multi-node training
We use ray for multi-node training.

```bash
bash train_multi_node.sh
```



## Evaluation

![Scaling law](assets/scaling_law.png)
![Rollout-128](assets/pass_128_results.png)

To evaluate the model, please input the log directory of the model you want to evaluate. The default folder name for the log directory is `logs` if you use the default training script.
```bash
python src/evaluation.py --workers 96 --folder_name logs/YOUR_LOG_DIR
```

Evaluation logs (in JSON format) will be saved to the `eval_logs` folder by default.

To visualize results:

```bash
python src/plot.py --file_list eval_logs/YOUR_SCORE_JSON_FILES
```


## Reference
This repository build on top of [LLaMA-Factory](https://github.com/hiyouga/LLaMA-Factory) and [Verl](https://github.com/volcengine/verl). 

The `verl/` directory is primarily copied from the Verl repository. We made modifications in the directory `verl/trainer/` and `verl/utils/reward_score/`.