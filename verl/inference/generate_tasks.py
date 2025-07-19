import os
import hydra
from omegaconf import DictConfig, OmegaConf
import json
from typing import List, Dict, Any

def get_model_path(exp_name: str) -> str:
    """Get the base model path based on experiment name."""
    if '0.5B' in exp_name:
        return "/oss/public/user/xuxu/distilled/ckpt_opt/SKD_RKL-0.5B_14B"
    elif '3B' in exp_name:
        return "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt"
    elif '7B' in exp_name:
        return "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-7B_5k_sft_opt"
    elif '14B' in exp_name:
        return "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-14B_5k_sft_opt"
    else:
        return "/nas/shared/sys2/liyizhi/LLaMA-Factory/saves/Qwen2.5-Coder-3B_5k_sft_opt"

def create_eval_tasks(
    base_paths: List[str],
    exp_names: List[str],
    global_steps: List[int],
    max_shot: int,
    base_config: DictConfig,
    prompt_types: List[str] = None
) -> List[Dict[str, Any]]:
    """Create evaluation tasks for all experiments and steps."""
    if prompt_types is None:
        prompt_types = ['sft'] * len(exp_names)
    
    if len(prompt_types) != len(exp_names):
        raise ValueError(f"Length of prompt_types ({len(prompt_types)}) must match length of exp_names ({len(exp_names)})")
    
    eval_tasks = []
    # Add SFT checkpoint task first
    eval_tasks.append({
        'model_path': get_model_path(exp_names[0]),
        'step': 0,
        'exp_name': 'sft_ckpt',
        'prompt_type': 'sft',
        'max_shot': max_shot,
        'output_dir': os.path.join(cfg.trainer.output_dir,"sft_ckpt"),
        'config': OmegaConf.to_container(base_config, resolve=True),
        'task_id': len(eval_tasks)
    })
    
    # Add tasks for each experiment and step
    for i, (base_path, exp_name, prompt_type) in enumerate(zip(base_paths, exp_names, prompt_types)):
        for step in global_steps:
            model_path = os.path.join(base_path, exp_name, f"global_step_{step}", "actor")
            if not os.path.exists(model_path):
                continue
            output_dir = os.path.join(cfg.trainer.output_dir, f"{exp_name}", f"{step_name}")
            if os.path.exists(model_path):
                eval_tasks.append({
                    'model_path': model_path,
                    'step': step,
                    'exp_name': exp_name,
                    'prompt_type': prompt_type,
                    'max_shot': max_shot,
                    'output_dir': output_dir,
                    'config': OmegaConf.to_container(base_config, resolve=True),
                    'task_id': len(eval_tasks)
                })
    
    return eval_tasks

@hydra.main(version_base=None, config_path="conf", config_name="config")
def main(cfg: DictConfig) -> None:
    """Generate evaluation tasks and save them to a JSON file."""
    # Extract configuration
    plot_cfg = cfg.get('plot', {})
    base_paths = plot_cfg.get('base_paths', ["/oss/public/user/chefengdi/ckpts"])
    exp_names = plot_cfg.get('exp_names', ["grpo_8nodes_5ksft_3B_spec_refine_one_score-ensures_fixed"])
    global_steps = plot_cfg.get('global_steps', [20, 40, 60])
    max_shot = max(plot_cfg.get('shot_numbers', [8]))
    prompt_types = plot_cfg.get('prompt_types', ['sft'] * len(exp_names))
    
    # Create tasks
    tasks = create_eval_tasks(base_paths, exp_names, global_steps, max_shot, cfg, prompt_types)
    
    # Save tasks to JSON file
    output_dir = '/nas/shared/sys2/chefengdi/eval_log/tasks/'
    os.makedirs(output_dir, exist_ok=True)
    tasks_file = os.path.join(output_dir, "eval_tasks.json")
    
    with open(tasks_file, 'w') as f:
        json.dump(tasks, f, indent=2)
    
    print(f"Generated {len(tasks)} evaluation tasks and saved to {tasks_file}")
    print("\nTask summary:")
    for task in tasks:
        print(f"Task {task['task_id']}: {task['exp_name']} step {task['step']} -> {task['model_path']}")

if __name__ == "__main__":
    main() 