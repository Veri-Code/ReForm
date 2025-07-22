# SFT via LLaMA-Factory

This project is based on [LLaMA-Factory](https://github.com/hiyouga/LLaMA-Factory) to enable efficient Supervised Fine-Tuning (SFT) workflows. For detailed usage, please refer to the [official documentation](https://llamafactory.readthedocs.io/zh-cn/latest/). We sincerely appreciate the excellent work of the LLaMA-Factory team! 👏

## Main Extensions in This Repository

- The `dafny_process/` directory provides data processing, format conversion, and automation scripts tailored for Dafny-related tasks.
- The `examples/train_full_opt/` directory contains our empirically optimal training hyperparameter configurations.
- The `data/processed_data/` directory includes newly processed datasets.
- Dependency requirements have been updated to include additional third-party libraries for the new features.

## Quick Start

1. **Install dependencies**
   ```bash
   pip install -r requirements.txt
   ```

2. **Edit and run the training script**
   Modify `dafny_process/src/scripts/run_train_sample.sh` to set your dataset and model paths as needed, then run:
   ```bash
   bash dafny_process/src/scripts/run_train_sample.sh
   ```

3. **Dataset and configuration notes**
   - `data/dataset_info.json` defines dataset names, file paths, and column mappings.
   - `examples/train_full_opt/` contains training parameter configuration files, with the base model path being the most important.

   > **Tip:** Since datasets are often iteratively updated, the `run_train_sample.sh` script uses the `sed -i` command to dynamically replace the dataset path. If you also need to frequently change the base model, you can use a similar approach.

## Key File Examples

**data/dataset_info.json**
```json
"opt_5k_vanilla_pure_remove_train": {
  "file_name": "processed_data/opt_5k_vanilla_pure_remove_train.json",
  "columns": {
    "prompt": "instruction",
    "query": "input",
    "response": "output",
    "system": "system",
    "history": "history"
  }
}
```

**examples/train_full_opt/ configuration snippet**
```yaml
model_name_or_path: Qwen2.5-Coder-0.5B
stage: sft
do_train: true
finetuning_type: full
deepspeed: examples/deepspeed/ds_z3_config.json

dataset: opt_5k_vanilla_pure_remove_train  # Dynamically replaced by script
template: qwen
cutoff_len: 16384
max_samples: 5000

output_dir: saves/Qwen2.5-Coder-0.5B_5k_sft_opt_v3
logging_steps: 1
plot_loss: true
save_only_model: true
save_strategy: epoch

per_device_train_batch_size: 8
gradient_accumulation_steps: 1
learning_rate: 0.1875e-4
num_train_epochs: 5
lr_scheduler_type: cosine
warmup_ratio: 0.1
bf16: true
ddp_timeout: 180000000

report_to: wandb
```

## Additional Notes

- For detailed data processing and automation script usage, please refer to `dafny_process/README.md`.
- To customize datasets or model configurations, refer to the above json/yaml examples.
- If you have any questions, feel free to open an issue or start a discussion.

---

If you need further details or want to expand a specific section, please let us know!
