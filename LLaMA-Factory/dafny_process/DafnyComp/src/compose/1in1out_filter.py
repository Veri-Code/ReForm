import json
from typing import List, Dict, Any
from utils import *

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def is_single_int_io(io_type: List[List[str]]) -> bool:
    """
    Check if all input and output types are single int
    Args:
        io_type: List of input and output types
    Returns:
        bool: True if all types are single int, False otherwise
    """
    # Convert IO types to dictionary format
    io_dict = convert_io_types_to_dict(io_type)
    
    # Check if there is exactly one input type and one output type
    if len(io_dict['Input']) != 1 or len(io_dict['Output']) != 1:
        return False
    
    # Check if both types are int
    input_type = io_dict['Input'][0]
    output_type = io_dict['Output'][0]
    
    return input_type == 'int' and output_type == 'int'

def filter_int_io_samples(input_file: str, output_file: str) -> None:
    """
    Filter samples where all IO types are single int and remove IO_sample field
    Args:
        input_file: Path to input JSONL file
        output_file: Path to output JSONL file
    """
    filtered_samples = []
    
    with open(input_file, 'r', encoding='utf-8') as f:
        for line in f:
            sample = json.loads(line.strip())
            if is_single_int_io(sample['IO_type']):
                filtered_samples.append(sample)
    
    # Write filtered samples to output file
    with open(output_file, 'w', encoding='utf-8') as f:
        for sample in filtered_samples:
            f.write(json.dumps(sample) + '\n')

if __name__ == '__main__':
    input_file = '../../raw_code/reformed_leetcodes.jsonl'
    output_file = '../../raw_code/filtered_int_io_testcases.jsonl'
    filter_int_io_samples(input_file, output_file)
