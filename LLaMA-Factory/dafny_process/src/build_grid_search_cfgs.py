import yaml
import copy
import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


# 1. Read yaml file
# 2. Modify parameters in yaml file
# 3. Save new yaml file


size = 0.5
version="pure"
task_type='sft'
base_cfg_path = f"../../examples/train_full_opt/qwen25code{size}B_full_sft.yaml"
set_path = f"../../examples/grid_search/qwen{size}B_{version}_{task_type}_grid_search"


# Read base_cfg_path
with open(base_cfg_path, "r") as f:
    base_cfg = yaml.load(f, Loader=yaml.FullLoader)

# Define parameters to modify
gradient_accumulation_steps = [1, 2, 4, 8]
learning_rate = [0.1875e-4 ,0.375e-4, 0.75e-4, 1.5e-4, 3e-4]
num_train_epochs = [5, 10]

dataset_list = [f"{task_type}_{version}_remove_train"]

for gcs in gradient_accumulation_steps:
    for lr in learning_rate:
        for ne in num_train_epochs:
            for ds in dataset_list:
                new_cfg = copy.deepcopy(base_cfg)
                new_cfg["gradient_accumulation_steps"] = gcs
                new_cfg["learning_rate"] = lr
                new_cfg["num_train_epochs"] = ne
                new_cfg["save_strategy"] = "no"
                new_cfg["dataset"] = ds
                new_cfg["output_dir"] = f"saves/qwen{size}B_grid_search_{ds}_gcs-{gcs}_lr-{lr}_epoch-{ne}_{task_type}"
                # Save new yaml file
                new_cfg_path = f"{set_path}/{ds}_gcs-{gcs}_lr-{lr:g}_epoch-{ne}.yaml"
                os.makedirs(os.path.dirname(new_cfg_path), exist_ok=True)
                with open(new_cfg_path, "w") as f:
                    yaml.dump(new_cfg, f)

