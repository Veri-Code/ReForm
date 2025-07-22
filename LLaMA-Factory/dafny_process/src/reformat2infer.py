import json
import re
import sys
import os

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.utils import *

with open('sft_format_data.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

# Inference data
infer_sample = {
        "org_input": "",
        "gt_output": "",
        "llm_input": "",
        "dafny_input": "",
        "output": {
            "llm_response": "",
            "dafny_response": {
                "status": "",
                "dafny_response": ""
            }
        },
        "stage_tag": "not_started",
        "org_input_id": "",
        "self_id": "",
        "self_tag": ""
    },

def json_dumper(data: list[dict], file_path: str):
    """
    Save data as JSON file with progress bar.
    
    Args:
        data: List of dictionaries to save
        file_path: Path where to save the file
    """
    total = len(data)
    print(f"Writing {total} records to {file_path}")
    
    with open(file_path, 'w', encoding='utf-8') as f:
        # Manually write JSON file to show progress
        f.write('[\n')
        
        for i, item in enumerate(data):
            json_str = json.dumps(item, ensure_ascii=False, indent=4)
            if i < total - 1:
                f.write(json_str + ',\n')
            else:
                f.write(json_str + '\n')
        
        f.write(']\n')
    
    print(f"Successfully saved {total} records")

infer_data = []
for idx, origin in enumerate(data):
    new_format = {
        "org_input": suffix_remove(origin['input']),
        "gt_output": origin['output'],
        # "gt_output": extract_dafny_code(origin['output']),
        "llm_input": "",
        "dafny_input": "",
        "output": {
            "llm_response": "",
            "dafny_response": {
                "status": "",
                "dafny_response": ""
            }
        },
        "stage_tag": "not_started",
        "org_input_id": idx,
        "self_id": idx * 10000,
        "self_tag": ""
    }
    infer_data.append(new_format)

json_dumper(infer_data, 'infer_format_data.json')