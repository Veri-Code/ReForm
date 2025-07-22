#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import List, Dict, Tuple, Any, Optional, Set
import json
from collections import Counter, defaultdict
import ast
import re
import os
import sys
from pathlib import Path
from utils import (
    jsonl_parser, clean_imports, find_missing_imports,
    add_imports, auto_import_file, 
    # shared imports
    add_shared_imports_to_file,
    get_recursive_needed_defs, SHARED_IMPORTS,
    # dynamic import mapping
    dynamic_mapper
)
from template import TEMPLATE_PATTERNS, DAG, generate_all_assignments
from tqdm import tqdm
import random
import subprocess
import tempfile
import shutil

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Templates to include
INCLUDED_TEMPLATES = [
    'main_2node_1',  # 2 nodes, single chain
    'main_3node_2',  # 3 nodes, single chain
    'main_4node_4',  # 4 nodes, single chain
    'main_5node_8',  # 5 nodes, single chain
]

class FunctionInfo:
    """Class to store information about a function"""
    def __init__(
        self,
        name: str,
        question_id: str,
        input_types: List[str],
        output_types: List[str],
        code: str,
        constraints: str,
        entry_point: str,
        io_sample: Any = None
    ):
        self.name = name
        self.question_id = question_id
        self.input_types = input_types
        self.output_types = output_types
        self.code = code
        self.constraints = constraints
        self.entry_point = entry_point
        self.io_sample = io_sample

def extract_function_name(signature: str) -> Tuple[str, str]:
    """
    Extract function name and question ID from signature
    Example: 'def function_name_123(x: int) -> int' -> ('function_name', '123')
    """
    # Remove 'class Solution:' if present
    signature = signature.replace('class Solution:', '').strip()
    print(f"Processing signature: {signature}")
    
    # Extract function name and question ID
    match = re.match(r'def\s+(\w+)_(\d+)', signature)
    if match:
        name, qid = match.group(1), match.group(2)
        print(f"Extracted name: {name}, question_id: {qid}")
        return name, qid
    print(f"No match found in signature: {signature}")
    return None, None

def parse_io_types(io_type: List[List[str]]) -> Tuple[List[str], List[str]]:
    """
    Parse IO types from the format [["n:int"], ["int"]]
    Returns: (input_types, output_types)
    """
    input_types = []
    output_types = []
    
    print(f"Parsing IO types: {io_type}")
    
    if len(io_type) >= 1:
        for input_type in io_type[0]:
            # Extract type after colon
            type_match = re.search(r':(\w+)', input_type)
            if type_match:
                input_types.append(type_match.group(1))
    
    if len(io_type) >= 2:
        output_types = io_type[1]
    
    return input_types, output_types

def parse_function_info(item: dict) -> Optional[FunctionInfo]:
    """
    Parse function information from a JSONL item
    """
    try:
        code = item.get('code', '')
        signature = item.get('signature', '')
        io_type = item.get('IO_type', [])
        constraints = item.get('constraints', '')
        entry_point = item.get('entry_point', '')
        io_sample = item.get('IO_sample', '')
        
        print(f"\nParsing function:")
        print(f"Entry point: {entry_point}")
        print(f"IO type: {io_type}")
        
        # Extract function name and question ID from entry_point
        # entry_point format: "function_name_question_id"
        parts = entry_point.split('_')
        if len(parts) != 2:
            print(f"Invalid entry point format: {entry_point}")
            return None
        
        func_name, question_id = parts[0], parts[1]
        print(f"Extracted name: {func_name}, question_id: {question_id}")
        
        # Parse IO types
        input_types, output_types = parse_io_types(io_type)
        print(f"Parsed input types: {input_types}")
        print(f"Parsed output types: {output_types}")
        
        return FunctionInfo(
            name=func_name,
            question_id=question_id,
            input_types=input_types,
            output_types=output_types,
            code=code,  # Keep the entire code content
            constraints=constraints,
            entry_point=entry_point,
            io_sample=io_sample
        )
    except Exception as e:
        print(f"Error parsing function: {e}")
        return None

def check_code_quality(code: str) -> Tuple[bool, str]:
    """
    Check code quality using flake8
    
    Args:
        code: Python code to check
        
    Returns:
        Tuple of (is_valid, error_message)
        - is_valid: True if code passes flake8 check
        - error_message: Error message if any, empty string if no errors
    """
    # Create a temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as temp_file:
        temp_file.write(code)
        temp_file_path = temp_file.name
    
    try:
        # Run flake8
        result = subprocess.run(['flake8', temp_file_path], 
                              capture_output=True, 
                              text=True)
        
        # Clean up temp file
        os.unlink(temp_file_path)
        
        if result.returncode == 0:
            return True, ""
        else:
            return False, result.stdout
    except Exception as e:
        # Clean up temp file in case of exception
        if os.path.exists(temp_file_path):
            os.unlink(temp_file_path)
        return False, str(e)

def process_generated_code(code: str, save_path: str) -> Tuple[bool, str]:
    """
    Process generated code by:
    1. Adding shared imports and cleaning unused ones
    2. Auto-importing missing imports using dynamic analysis
    3. Formatting with black
    """
    try:
        # 1. Analyze what shared definitions are needed
        needed_defs = get_recursive_needed_defs(code, SHARED_IMPORTS)
        # 2. Add shared imports if needed
        if needed_defs:
            # Create temp directory if it doesn't exist
            temp_dir = "../../tmp"
            os.makedirs(temp_dir, exist_ok=True)
            temp_file = os.path.join(temp_dir, "temp_code.py")
            with open(temp_file, 'w', encoding='utf-8') as f:
                f.write(code)
            add_shared_imports_to_file(temp_file)
            with open(temp_file, 'r', encoding='utf-8') as f:
                code_with_shared = f.read()
            os.remove(temp_file)
        else:
            code_with_shared = code
        # 3. Clean imports and add missing ones using dynamic analysis
        cleaned_code = clean_imports(code_with_shared)
        missing_imports, current_imports = find_missing_imports(cleaned_code)
        if missing_imports:
            cleaned_code = add_imports(cleaned_code, missing_imports, current_imports)
        # 4. Format with black
        # Create temp directory if it doesn't exist
        temp_dir = "../../tmp"
        os.makedirs(temp_dir, exist_ok=True)
        temp_file = os.path.join(temp_dir, "temp_code.py")
        with open(temp_file, 'w', encoding='utf-8') as f:
            f.write(cleaned_code)
        subprocess.run(['black', temp_file], check=True, capture_output=True)
        with open(temp_file, 'r', encoding='utf-8') as f:
            formatted_code = f.read()
        os.remove(temp_file)
        return True, formatted_code
    except Exception as e:
        print(f"Warning: Processing failed: {str(e)}")
        return False, cleaned_code  # Return cleaned but unformatted code if processing fails

def generate_composed_code_and_meta(assignment, dag, functions, template_name, template_info, subdir_path: str):
    """
    Generate composed code and meta information
    
    Args:
        assignment: Function assignment for the DAG
        dag: DAG structure
        functions: List of available functions
        template_name: Name of the template
        template_info: Template information
        subdir_path: Path where the code should be saved
    """
    # 1. Flatten assignment to get function indices for each node
    flat_assignment = []
    for group in assignment:
        flat_assignment.extend(group)
    # 2. Get node order using level_order
    node_order = dag.level_order()
    # 3. Generate question_id order
    question_id_order = [functions[idx].question_id for idx in flat_assignment]
    # 4. Generate code and meta information
    # 4.1 Generate function name assignments
    node2func = {node: functions[idx] for node, idx in zip(node_order, flat_assignment)}
    # 4.2 Generate all function code (with constraint comments)
    code_blocks = []
    used_funcs = set()
    for node in node_order:
        func = node2func[node]
        if func.entry_point not in used_funcs:
            code_lines = func.code.split('\n')
            for i, line in enumerate(code_lines):
                if line.strip().startswith(f'def {func.entry_point}'):
                    code_lines.insert(i + 1, f'    # {func.constraints}')
                    break
            code_blocks.append('\n'.join(code_lines))
            used_funcs.add(func.entry_point)
    # 4.3 Generate main composition function
    main_code = f"\ndef {template_name}(o: object) -> object:\n"
    main_code += f'    """{template_info["description"]}"""\n'
    # pattern: list of (parent, child)
    var_map = {}  # node -> variable name
    for idx, node in enumerate(node_order):
        var_map[node] = f'o{idx+1}'
    # Generate variable assignments
    for (parent, child) in template_info['pattern']:
        func = node2func[child]
        if parent is None:
            main_code += f"    {var_map[child]}: object = {func.entry_point}(o)\n"
        else:
            main_code += f"    {var_map[child]}: object = {func.entry_point}({var_map[parent]})\n"
    # Generate return statement
    return_vars = [var_map[node] for node in template_info['return_nodes']]
    if len(return_vars) == 1:
        main_code += f"    return {return_vars[0]}\n"
    else:
        main_code += f"    return ({', '.join(return_vars)})\n"
    code_blocks.append(main_code)
    composed_code = '\n\n'.join(code_blocks)
    
    # 5. Process the generated code
    subdir_name = f"{template_name}-{'-'.join(question_id_order)}"
    py_filepath = os.path.join(subdir_path, f"{subdir_name}.py")
    success, processed_code = process_generated_code(composed_code, py_filepath)
    
    # Generate meta information (always needed for return)
    meta_info = [functions[idx].__dict__ for idx in flat_assignment]
    
    if success:
        # Save code and meta information
        with open(py_filepath, 'w') as f:
            f.write(processed_code)
        
        # Save meta information
        meta_filepath = os.path.join(subdir_path, 'compositions.jsonl')
        with open(meta_filepath, 'w') as f:
            for info in meta_info:
                f.write(json.dumps(info) + '\n')
    
    return processed_code, meta_info, question_id_order

def main():
    # Load and analyze code samples
    print("Loading data from filtered_int_io.jsonl...")
    data = jsonl_parser('../../raw_code/filtered_int_io_testcases.jsonl')
    print(f"Loaded {len(data)} items from JSONL")
    
    # Parse functions from data
    functions = []
    for item in data:
        func_info = parse_function_info(item)
        if func_info:
            functions.append(func_info)
    
    print(f"Successfully parsed {len(functions)} functions")
    print("Available functions:")
    for func in functions:
        print(f"- {func.entry_point}")
    
    # Set composition directory
    composition_dir = '../../DfyAutoSpec_wtc_chain300'
    os.makedirs(composition_dir, exist_ok=True)  # Ensure the top-level directory exists
    
    # Generate compositions for each template
    compositions_count = 0
    print("\nGenerating compositions...")
    print(f"Including templates: {', '.join(INCLUDED_TEMPLATES)}")
    
    # Filter out excluded templates
    available_templates = {name: info for name, info in TEMPLATE_PATTERNS.items() 
                        if name in INCLUDED_TEMPLATES}
    
    for template_name, template_info in tqdm(available_templates.items(), desc='Templates'):
        pattern = template_info['pattern']
        dag = DAG(pattern)
        # Only sample at leaf sibling combinations
        all_assignments = generate_all_assignments(functions, dag, max_leaf_combos=5)
        # If the number of combinations is greater than 'max_assignments', randomly sample 'max_assignments'
        max_assignments = 500
        # max_assignments = 99999999
        if len(all_assignments) > max_assignments:
            sampled_assignments = random.sample(all_assignments, max_assignments)
        else:
            sampled_assignments = all_assignments
        for assignment in tqdm(sampled_assignments, desc=f'{template_name} assignments', leave=False):
            # Create folder name
            question_id_order = [functions[idx].question_id for idx in [idx for group in assignment for idx in group]]
            subdir_name = f"{template_name}-{'-'.join(question_id_order)}"
            subdir_path = os.path.join(composition_dir, subdir_name)
            os.makedirs(subdir_path, exist_ok=True)
            
            composed_code, meta_info, question_id_order = generate_composed_code_and_meta(
                assignment, dag, functions, template_name, template_info, subdir_path)
            
            # Save meta information
            meta_filepath = os.path.join(subdir_path, 'compositions.jsonl')
            with open(meta_filepath, 'w') as f:
                for info in meta_info:
                    f.write(json.dumps(info) + '\n')
            compositions_count += 1
    
    print(f"\nGenerated {compositions_count} composed functions in subdirectories under {composition_dir}")
    print(f"Used {len(available_templates)} templates (excluded {len(EXCLUDED_TEMPLATES)} templates)")

if __name__ == "__main__":
    main()
