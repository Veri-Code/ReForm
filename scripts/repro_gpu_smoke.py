import argparse
import os
from pathlib import Path

import pandas as pd
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer


def main():
    parser = argparse.ArgumentParser(description="GPU smoke test for Re:Form reproduction assets.")
    parser.add_argument("--model_path", default="sft_ckpts/sft_0.5B")
    parser.add_argument("--parquet", default="repro_artifacts/verl_smoke_dataset_20260507/test.parquet")
    parser.add_argument("--max_new_tokens", type=int, default=24)
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    model_path = repo_root / args.model_path
    parquet_path = repo_root / args.parquet
    dafny_dir = repo_root / "hf_assets" / "tools" / "dafny-4.11.0" / "dafny"
    os.environ["PATH"] = f"{dafny_dir}{os.pathsep}{os.environ.get('PATH', '')}"
    os.environ.setdefault("DOTNET_SYSTEM_GLOBALIZATION_INVARIANT", "1")
    os.environ.setdefault("REFORM_REWARD_LOG_DIR", str(repo_root / "repro_artifacts" / "gpu_reward_logs_20260507"))

    print(f"repo_root={repo_root}")
    print(f"model_path={model_path}")
    print(f"parquet_path={parquet_path}")
    print(f"dafny_dir={dafny_dir}")

    if not torch.cuda.is_available():
        raise RuntimeError("CUDA is not available; submit this script through SiFlow.")

    print(f"cuda_device_count={torch.cuda.device_count()}")
    print(f"cuda_device_name={torch.cuda.get_device_name(0)}")

    tokenizer = AutoTokenizer.from_pretrained(model_path, trust_remote_code=True)
    dtype = torch.bfloat16 if torch.cuda.is_bf16_supported() else torch.float16
    model = AutoModelForCausalLM.from_pretrained(
        model_path,
        torch_dtype=dtype,
        trust_remote_code=True,
    ).to("cuda")
    model.eval()

    row = pd.read_parquet(parquet_path).iloc[0]
    prompt = row["prompt"][0]["content"]
    inputs = tokenizer(prompt, return_tensors="pt").to("cuda")
    with torch.no_grad():
        outputs = model.generate(
            **inputs,
            max_new_tokens=args.max_new_tokens,
            do_sample=False,
            pad_token_id=tokenizer.eos_token_id,
        )
    generated = tokenizer.decode(outputs[0][inputs["input_ids"].shape[-1]:], skip_special_tokens=True)
    print(f"generated_token_count={outputs.shape[-1] - inputs['input_ids'].shape[-1]}")
    print("generated_preview_start")
    print(generated[:1000])
    print("generated_preview_end")

    from verl.utils.reward_score import subset_reward

    fence = chr(96) * 3
    solution = prompt + "<answer>" + fence + "dafny\n" + row["output"] + "\n" + fence + "</answer>"
    score = subset_reward.compute_score(
        solution,
        row["reward_model"]["ground_truth"],
        exp_name="gpu_reward_smoke",
        index=0,
        version="one_score",
    )
    print(f"ground_truth_reward_smoke={score}")


if __name__ == "__main__":
    main()
