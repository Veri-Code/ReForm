import os
import sys
import argparse
from typing import List, Dict

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.utils import *

def is_code_line(line: str, in_block_comment: bool) -> tuple[bool, bool]:
    stripped_line = line.strip()
    if stripped_line.startswith('//'):
        return False, in_block_comment
    if stripped_line.startswith('/*'):
        return False, True
    if stripped_line.endswith('*/'):
        return False, False
    if in_block_comment:
        return False, in_block_comment
    return True, in_block_comment

def count_code_lines(code: str) -> int:
    in_block_comment = False
    code_lines = 0
    for line in code.split('\n'):
        is_code, in_block_comment = is_code_line(line, in_block_comment)
        if is_code and line.strip():  # Only count non-empty code lines
            code_lines += 1
    return code_lines

def filter_trivial_code(data: List[Dict], min_lines: int = 10) -> List[Dict]:
    """
    Filter out entries with fewer than specified lines of actual code
    Args:
        data: List of dictionaries containing Dafny code
        min_lines: Minimum number of code lines required (default: 10)
    Returns:
        Filtered list of entries
    """
    filtered_data = []
    for entry in data:
        # Check if the entry contains Dafny code
        code = entry.get('dafny') or entry.get('input')
        if code and count_code_lines(code) >= min_lines:
            filtered_data.append(entry)
        else:
            print(f"Filtered out entry with insufficient code lines")
    return filtered_data

def parse_arguments() -> argparse.Namespace:
    """
    Parse command line arguments
    Returns:
        Parsed arguments namespace
    """
    parser = argparse.ArgumentParser(description='Filter Dafny code entries based on minimum code lines')
    parser.add_argument('--input', '-i', type=str, default='input_file.json',
                      help='Input JSON file path')
    parser.add_argument('--output', '-o', type=str, default='output_file.json',
                      help='Output JSON file path')
    parser.add_argument('--min-lines', '-m', type=int, default=10,
                      help='Minimum number of code lines required (default: 10)')
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_arguments()
    
    # Process the data
    data = json_parser(args.input)
    print(f"Processing {len(data)} entries...")
    filtered_data = filter_trivial_code(data, args.min_lines)
    print(f"Retained {len(filtered_data)} entries after filtering")
    json_dumper(filtered_data, args.output)

