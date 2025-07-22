import json
from pathlib import Path
import time
from contextlib import contextmanager
import pandas as pd
from rich import print as rprint
from tqdm import tqdm  # Import tqdm library
import logging

### 1. Parsing Utils.
def parquet_parser(file_path: str) -> list[dict]:
    """
    Parse parquet file and convert to list of dictionaries.
    
    Args:
        file_path: Path to the parquet file
        
    Returns:
        List of dictionaries with the parsed data
    """
    print(f"Reading parquet file: {file_path}")
    df = pd.read_parquet(file_path)
    print(f"Loaded {len(df)} records")
    return df.to_dict(orient='records')

def jsonl_parser(file_path: str) -> list[dict]:
    """
    Parse JSONL file with progress bar.
    
    Args:
        file_path: Path to the JSONL file
        
    Returns:
        List of dictionaries with the parsed data
    """
    # First count total lines for progress bar
    with open(file_path, 'r', encoding='utf-8') as f:
        total_lines = sum(1 for line in f if line.strip())
    
    result = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in tqdm(f, total=total_lines, desc="Parsing JSONL"):
            if line.strip():
                result.append(json.loads(line))
    return result

def json_parser(file_path: str) -> list[dict]:
    """
    Parse JSON file and convert to list of dictionaries.
    
    Args:
        file_path: Path to the JSON file
        
    Returns:
        List of dictionaries with the parsed data
    """
    print(f"Reading JSON file: {file_path}")
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    print(f"Loaded {len(data)} records")
    return data

def judge_file_format(filepath):
    """
    Determine the format of a file based on its extension and content.
    
    Args:
        filepath: Path to the file
        
    Returns:
        String indicating file format: 'json', 'jsonl', or None if unsupported
    """
    if filepath.endswith('.jsonl'):
        return 'jsonl'
    elif filepath.endswith('.json'):
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = [line for line in f if line.strip()]
            if len(lines) == 1:
                return 'json'
            if all(line.lstrip().startswith('{') for line in lines):
                return 'jsonl'
        return 'json'
    else:
        return None

def file_parser(file_path: str) -> list[dict]:
    """
    Generic file parser that determines format and parses accordingly.
    
    Args:
        file_path: Path to the file
        
    Returns:
        List of dictionaries with the parsed data
    """
    file_format = judge_file_format(file_path)
    if file_format == 'jsonl':
        return jsonl_parser(file_path)
    elif file_format == 'json':
        return json_parser(file_path)
    else:
        raise ValueError(f"Only Json/Jsonl Files are Supported!")

def jsonl_dumper(data: list[dict], file_path: str):
    """
    Save data as JSONL file with progress bar.
    
    Args:
        data: List of dictionaries to save
        file_path: Path where to save the file
    """
    file_path = Path(file_path).with_suffix('.jsonl')
    total = len(data)
    print(f"Writing {total} records to {file_path}")
    
    with open(file_path, 'w', encoding='utf-8') as f:
        for item in tqdm(data, total=total, desc="Writing JSONL"):
            f.write(json.dumps(item, ensure_ascii=False) + '\n')
    
    print(f"Successfully saved {total} records")

def json_dumper(data: list[dict], file_path: str):
    """
    Save data as JSON file with progress bar.
    
    Args:
        data: List of dictionaries to save
        file_path: Path where to save the file
    """
    file_path = Path(file_path).with_suffix('.json')
    total = len(data)
    print(f"Writing {total} records to {file_path}")
    
    with open(file_path, 'w', encoding='utf-8') as f:
        # Manually write JSON file to show progress
        f.write('[\n')
        
        for i, item in enumerate(tqdm(data, desc="Writing JSON")):
            json_str = json.dumps(item, ensure_ascii=False, indent=4)
            if i < total - 1:
                f.write(json_str + ',\n')
            else:
                f.write(json_str + '\n')
        
        f.write(']\n')
    
    print(f"Successfully saved {total} records")

def file_dumper(data: list[dict], file_path: str):
    """
    Generic file dumper that selects the appropriate format based on file extension.
    
    Args:
        data: List of dictionaries to save
        file_path: Path where to save the file
    """
    total = len(data)
    print(f"Writing {total} records to {file_path}")
    
    if file_path.endswith('.jsonl'):
        with open(file_path, 'w', encoding='utf-8') as f:
            for item in tqdm(data, desc="Writing JSONL"):
                f.write(json.dumps(item, ensure_ascii=False) + '\n')
    elif file_path.endswith('.json'):
        with open(file_path, 'w', encoding='utf-8') as f:
            # Manually write JSON file to show progress
            f.write('[\n')
            
            for i, item in enumerate(tqdm(data, desc="Writing JSON")):
                json_str = json.dumps(item, ensure_ascii=False, indent=4)
                if i < total - 1:
                    f.write(json_str + ',\n')
                else:
                    f.write(json_str + '\n')
            
            f.write(']\n')
    else:
        raise ValueError(f"Only Json/Jsonl Files are Supported!")
    
    print(f"Successfully saved {total} records")

### 2. Timer
@contextmanager
def timer_context(description: str):
    '''
    Timer for measuring execution time of code blocks.
    
    Args:
        description: Description of the timed operation
    '''
    start_time = time.time()
    try:
        yield
    finally:
        end_time = time.time()
        elapsed_time = end_time - start_time
        rprint(f"{description} took {elapsed_time:.2f} seconds.\n")