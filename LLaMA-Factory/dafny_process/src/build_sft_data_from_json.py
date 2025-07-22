import os 
import random
import sys

from colorama import Fore, Style
from tqdm import tqdm  
from transformers import AutoTokenizer
from uuid import uuid4

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.utils import *

random.seed(42)

# Define custom color palette from dark to light
INFO_DARK = Fore.BLUE       # Darkest - for less important information
INFO_MID = Fore.CYAN        # Middle darkness - for normal information
SUCCESS = Fore.GREEN        # For success messages
WARNING = Fore.YELLOW       # For warnings
ERROR = Fore.LIGHTRED_EX    # Brightest - for errors and important warnings
RESET = Style.RESET_ALL     # Reset color

SYS_DAFNY = "You are an expert in Dafny. \
You will be given tasks dealing with Dafny programs including precise annotations. \
You should only return code body in all circumstances. No text is allowed.\n"

GEN_HINTS_FROM_BODY = "Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. \
Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. \
Do not explain or output any text. If you have to explain, put all explanations in comments form. \
There should only be code body in your output. \
Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. \
Below is the program:\n```dafny\n"

# Mainly for initial pybased data. After that, the format is [{'dafny': '...'}, ...]
def get_dfy_files(directory):
    dfy_files = []
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith('.dfy'):
                dfy_files.append(os.path.join(root, file))
    return dfy_files

def convert_item(item):
    for sub_item in item["dafny"]:
        if sub_item["code_state"] == "vanilla":
            # Ensure comments are removed from ground truth
            cleaned_code = sub_item["code_content"]
            item["ground_truth"] = cleaned_code
        else:
            # Ensure comments are removed from input
            cleaned_code = sub_item["code_content"]
            item["input"] = cleaned_code

    return {
        "instruction": GEN_HINTS_FROM_BODY,
        "input": item["input"] + "\n```",
        "output": "```dafny\n" + item["ground_truth"] + "\n```",
        "system": SYS_DAFNY,
        "history": [],
        "uuid": item["uuid"],
        "file": item.get("file", "N/A"),
        "source": item.get("source", "unknown")
    }

# Add safe tokenizer function
def safe_tokenize(text, tokenizer, max_length=32000):
    """Safely tokenize text and handle long sequences"""
    try:
        tokens = tokenizer(text, truncation=True, max_length=max_length).input_ids
        return tokens
    except Exception as e:
        print(ERROR, f"Tokenization error: {e}", RESET)
        # Split text and process in chunks
        half_len = len(text) // 2
        first_half = text[:half_len]
        tokens_first = tokenizer(first_half, truncation=True, max_length=max_length//2).input_ids
        return tokens_first  # Return at least half of the tokens

### Dafny Files Input Dir, Custom
# dir_path = '...'
# dfy_files = get_dfy_files(dir_path)

remove_keywords = ["requires", 
                   "ensures", 
                   "invariant", 
                   "assert", 
                   "modifies" 
                   ,"assume", 
                   "reads", 
                   "decreases"]

# Add code length check function
def check_code_length(code, max_chars=100000):
    if len(code) > max_chars:
        print(WARNING, f"Warning: Code too long ({len(code)} chars). Truncating...", RESET)
        return code[:max_chars]
    return code

pure_data = []

# Create a list to store raw samples that are too long
long_raw_samples = []

# Create a dictionary to track original samples by UUID
original_samples = {}

all_dafny = json_parser('../raw_dataset/sft_data_5150.json')

# First pass: clean all samples and store the cleaned versions
print(INFO_MID, "First pass: Cleaning all samples...", RESET)
cleaned_samples = []

for item in tqdm(all_dafny, desc='Cleaning samples'):
    code = item['dafny']
    # Check and limit code length
    code = check_code_length(code)
    
    # Clean the code first (remove comments, dependencies and extra empty lines)
    cleaned_code = emptyline_remove(depend_remove(comment_remove(code)))
    
    # Generate a UUID to track this sample
    sample_uuid = str(uuid4())
    
    # Store the cleaned sample
    cleaned_sample = {
        'source': 'Native Dafny & Python2Dafny',
        'uuid': sample_uuid,
        'original_dafny': code,
        'cleaned_dafny': cleaned_code  # Store the cleaned version as the "raw" sample
    }
    
    # Add to cleaned samples list
    cleaned_samples.append(cleaned_sample)
    
    # Store in dictionary for quick lookup by UUID
    original_samples[sample_uuid] = cleaned_sample

# Second pass: process cleaned samples to create partial and pure versions
print(INFO_MID, "Second pass: Creating pure version sft data...", RESET)
for cleaned_sample in tqdm(cleaned_samples, desc='Processing'):
    sample_uuid = cleaned_sample['uuid']
    cleaned_code = cleaned_sample['cleaned_dafny']

    pure_form = {
        'source': 'Native Dafny & Python2Dafny',
        'uuid': sample_uuid,  # Use the same UUID to track back to original
        'dafny': [
            {"code_content": cleaned_code, 
            "code_state": "vanilla"}, 
            {"code_content": hint_remove_pure(cleaned_code,
                                        remove_keywords=remove_keywords), 
            "code_state": "vanilla_pure_remove"}],
    }
    
    pure_data.append(pure_form)
           
# Check same content.
same_cnt_pure = 0
for item in tqdm(pure_data[:], desc='Checking pure'):

    if item['dafny'][0]['code_content'] == item['dafny'][1]['code_content']:
        print(INFO_DARK, f"-- Same Content in Pure --: \n\n {item['dafny'][0]['code_content'][:200]} ... \n\n", RESET)
        pure_data.remove(item)
        same_cnt_pure += 1
print(INFO_MID, f"== After pure remove {same_cnt_pure} items remain the same. Filtered. ==", RESET)

# Load tokenizer with reasonable truncation length
print(INFO_MID, "Loading tokenizer...", RESET)
tokenizer = AutoTokenizer.from_pretrained("/nas/shared/sys2/liyizhi/models/Qwen2.5-Coder-0.5B", trust_remote_code=True)
truncate_len = 16384  # Length limit for training samples
model_max_len = 32768  # Maximum length for tokenizer

random.shuffle(pure_data)
train_data_pure = []
dev_data_pure = []
token_lens = []

# Set to track UUIDs of long samples to avoid duplicate processing
long_sample_uuids = set()

print(INFO_MID, "Processing pure data...", RESET)
max_token_len = 0
max_token_item = None
skipped_pure_count = 0

for i, item in enumerate(tqdm(pure_data, desc="Processing pure data")):
    converted_item = convert_item(item)
    full_text = converted_item["system"] + converted_item["instruction"] + converted_item["input"] + converted_item["output"]
    
    # Use safe tokenizer function
    tokens = safe_tokenize(full_text, tokenizer, model_max_len)
    token_len = len(tokens)
    token_lens.append(token_len)
    
    # Record the longest sample
    if token_len > max_token_len:
        max_token_len = token_len
        max_token_item = converted_item
    
    if token_len >= truncate_len:
        print(WARNING, f"Skipping item with {token_len} tokens (> {truncate_len})", RESET)
        # Get the UUID to find original sample
        sample_uuid = item["uuid"]
        
        # Only process this long sample if we haven't seen it before
        if sample_uuid not in long_sample_uuids:
            # Get the original raw sample
            original_sample = original_samples.get(sample_uuid)
            if original_sample:
                # Add token length info to the raw sample
                original_sample["token_length"] = token_len
                # Add to long raw samples list
                long_raw_samples.append(original_sample)
                # Mark as processed
                long_sample_uuids.add(sample_uuid)
                
        skipped_pure_count += 1
        continue
    
    # Custom the dev/train split
    if len(dev_data_pure) < 0:
        dev_data_pure.append(converted_item)
    else:
        train_data_pure.append(converted_item)

print(SUCCESS, f"Overall max token length: {max_token_len}", RESET)
print(WARNING, f"Skipped {skipped_pure_count} pure samples due to length", RESET)
print(WARNING, f"Total unique long raw samples saved: {len(long_raw_samples)}", RESET)

if max_token_len > model_max_len:
    print(ERROR, f"Warning: Some items still exceed model max length ({model_max_len})", RESET)
    if max_token_item:
        print(ERROR, f"Example item: source={max_token_item.get('source')}, uuid={max_token_item.get('uuid')}", RESET)

## SFT Data Output Dir, Custom
output_dev_file_pure=f'../../data/processed_data/opt_5k_vanilla_pure_remove_dev.json'
output_train_file_pure=f'../../data/processed_data/opt_5k_vanilla_pure_remove_train.json'
output_long_raw_samples=f'../../data/processed_data/opt_5k_long_raw_samples.json'

print(SUCCESS, "Saving processed data...", RESET)
json_dumper(train_data_pure, output_train_file_pure)

if len(dev_data_pure) > 0:
    json_dumper(dev_data_pure, output_dev_file_pure)

# Save long raw samples
if len(long_raw_samples) > 0:
    json_dumper(long_raw_samples, output_long_raw_samples)

print(SUCCESS, f"Processing complete. Created:", RESET)
print(f"- {len(train_data_pure)} training samples (pure)")
print(f"- {len(dev_data_pure)} dev samples (pure)")
print(f"- {len(long_raw_samples)} long raw samples (skipped)")