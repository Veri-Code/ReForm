import os 
import sys

from tqdm import tqdm  

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.utils import *

total = json_parser("input_sft/infer_file.json")

length = len(total)

extracted = []
for item in tqdm(total, desc="extracting dafny code"):

    if 'gt_output' in item.keys():
        print('Extracting Inference Format data..')
        code = item.get('gt_output')
    elif 'output' in item.keys() and isinstance(item.get('output'), str):
        print('Extracting SFT Format data..')
        code_field = item.get('output')
        code = extract_dafny_code(code_field)
    else:
        raise ValueError(f"No code field found in item: {item}")
    extracted.append({'dafny': code})

json_dumper(extracted, f"extracted_raw_dafny.json")
