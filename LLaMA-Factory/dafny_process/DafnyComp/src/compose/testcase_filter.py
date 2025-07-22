"""
Testcase filter based on root function IO constraints.
This code only validates if root function testcases satisfy their IO constraints,
since all constraint conflicts are already reflected in the root function's constraints.
"""

import json
import re
import ast
from typing import Dict, List, Any, Tuple, Optional
import os
from pathlib import Path
import subprocess
import tempfile
import shutil
import time
from tqdm import tqdm
import multiprocessing as mp
from functools import partial
import logging
import argparse
import sys
import os

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class SimpleConstraintValidator:
    """Simple validator for checking if input/output values satisfy constraints"""
    
    def __init__(self):
        self.constraint_patterns = {
            'range': r'(\d+)\s*<=\s*(\w+)\s*<=\s*(\d+)',
            'single_range': r'(\w+)\s*<=\s*(\d+)',
            'single_range_reverse': r'(\d+)\s*<=\s*(\w+)',
            'output_range': r'(\d+)\s*<=\s*<output>\s*<=\s*(\d+)',
            'output_single_upper': r'<output>\s*<=\s*(\d+)',
            'output_single_lower': r'(\d+)\s*<=\s*<output>',
            'output_equals': r'<output>\s*[=!]=\s*([^<>\s]+)',
            'output_not_equals': r'<output>\s*!=\s*([^<>\s]+)',
            'output_type': r'<output>\s+is\s+(\w+)',
            'output_boolean': r'<output>\s+is\s+(True|False)',
            'output_length': r'len\s*\(\s*<output>\s*\)\s*<=\s*(\d+)',
            'output_string_length': r'len\s*\(\s*<output>\s*\)\s*<=\s*(\d+)',
            'unconstrained': r'unconstrained',
            'power_expression': r'(\d+)\*\*(\d+)',
        }
    
    def parse_constraint(self, constraint: str) -> Dict[str, Tuple[Optional[int], Optional[int]]]:
        """Parse constraint string and return variable bounds"""
        bounds = {}
        
        if not constraint or constraint.strip() == "":
            return bounds
        
        # Handle power expressions like 2**31 - 1
        def eval_power(expr: str) -> int:
            try:
                if '**' in expr:
                    base, exp = expr.split('**')
                    result = int(base) ** int(exp)
                    # Check if result is reasonable (avoid overflow)
                    if result > 2**63 - 1:  # Max safe integer
                        print(f"Warning: Power expression {expr} results in very large number, using safe default")
                        return 2**31 - 1  # Use max int32 as safe default
                    return result
                return int(expr)
            except (ValueError, OverflowError) as e:
                print(f"Warning: Could not evaluate power expression '{expr}': {e}")
                # Return a reasonable default based on common constraint patterns
                if '31' in expr or '32' in expr:
                    return 2**31 - 1  # Max int32
                elif '63' in expr or '64' in expr:
                    return 2**63 - 1  # Max int64
                else:
                    return 2**31 - 1  # Default to max int32
        
        # Replace power expressions
        constraint = re.sub(r'(\d+\*\*\d+)', lambda m: str(eval_power(m.group(1))), constraint)
        
        # Handle unconstrained
        if re.search(self.constraint_patterns['unconstrained'], constraint, re.IGNORECASE):
            return bounds
        
        # Handle range constraints like "1 <= n <= 200"
        range_match = re.search(self.constraint_patterns['range'], constraint)
        if range_match:
            var_name = range_match.group(2)
            min_val = int(range_match.group(1))
            max_val = int(range_match.group(3))
            bounds[var_name] = (min_val, max_val)
            return bounds
        
        # Handle single bound constraints like "n <= 200"
        single_match = re.search(self.constraint_patterns['single_range'], constraint)
        if single_match:
            var_name = single_match.group(1)
            max_val = int(single_match.group(2))
            bounds[var_name] = (None, max_val)
            return bounds
        
        # Handle reverse single bound constraints like "1 <= n"
        reverse_match = re.search(self.constraint_patterns['single_range_reverse'], constraint)
        if reverse_match:
            min_val = int(reverse_match.group(1))
            var_name = reverse_match.group(2)
            bounds[var_name] = (min_val, None)
            return bounds
        
        # Handle output range constraints like "2 <= <output> <= 15"
        output_match = re.search(self.constraint_patterns['output_range'], constraint)
        if output_match:
            min_val = int(output_match.group(1))
            max_val = int(output_match.group(2))
            bounds['<output>'] = (min_val, max_val)
            return bounds
        
        # Handle output single upper bound like "<output> <= 100"
        output_upper_match = re.search(self.constraint_patterns['output_single_upper'], constraint)
        if output_upper_match:
            max_val = int(output_upper_match.group(1))
            bounds['<output>'] = (None, max_val)
            return bounds
        
        # Handle output single lower bound like "1 <= <output>"
        output_lower_match = re.search(self.constraint_patterns['output_single_lower'], constraint)
        if output_lower_match:
            min_val = int(output_lower_match.group(1))
            bounds['<output>'] = (min_val, None)
            return bounds
        
        # Handle output equals constraint like "<output> = 42" or "<output> == 42"
        output_equals_match = re.search(self.constraint_patterns['output_equals'], constraint)
        if output_equals_match:
            try:
                equal_val = int(output_equals_match.group(1))
                bounds['<output>'] = (equal_val, equal_val)  # min = max for equality
                return bounds
            except ValueError:
                # If not a number, store as string constraint
                bounds['<output>_equals'] = output_equals_match.group(1)
                return bounds
        
        # Handle output not equals constraint like "<output> != 0"
        output_not_equals_match = re.search(self.constraint_patterns['output_not_equals'], constraint)
        if output_not_equals_match:
            try:
                not_equal_val = int(output_not_equals_match.group(1))
                bounds['<output>_not_equals'] = not_equal_val
                return bounds
            except ValueError:
                bounds['<output>_not_equals_str'] = output_not_equals_match.group(1)
                return bounds
        
        # Handle output type constraint like "<output> is int"
        output_type_match = re.search(self.constraint_patterns['output_type'], constraint)
        if output_type_match:
            bounds['<output>_type'] = output_type_match.group(1)
            return bounds
        
        # Handle output boolean constraint like "<output> is True"
        output_bool_match = re.search(self.constraint_patterns['output_boolean'], constraint)
        if output_bool_match:
            bounds['<output>_boolean'] = output_bool_match.group(1)
            return bounds
        
        # Handle output length constraint like "len(<output>) <= 10"
        output_length_match = re.search(self.constraint_patterns['output_length'], constraint)
        if output_length_match:
            max_length = int(output_length_match.group(1))
            bounds['<output>_max_length'] = max_length
            return bounds
        
        return bounds
    
    def extract_value(self, value_str: str) -> Optional[Any]:
        """Extract value from string like 'n = 100' or just '100'"""
        try:
            # Try to evaluate the value
            return ast.literal_eval(value_str.strip())
        except (ValueError, SyntaxError):
            # If literal_eval fails, try to parse as integer
            try:
                return int(value_str.strip())
            except ValueError:
                return None
    
    def extract_input_value(self, input_str: str) -> Dict[str, Any]:
        """Extract input values from input string like 'n = 100'"""
        try:
            # Parse input string like "n = 100" or "x = -123"
            parts = input_str.split('=', 1)
            if len(parts) != 2:
                return {}
            
            var_name = parts[0].strip()
            value = self.extract_value(parts[1])
            if value is not None:
                return {var_name: value}
        except Exception:
            pass
        return {}
    
    def validate_value(self, value: Any, bounds: Tuple[Optional[int], Optional[int]]) -> bool:
        """Validate if value satisfies the bounds"""
        min_val, max_val = bounds
        
        # Handle tuple output (common in main functions)
        if isinstance(value, tuple):
            # For tuple output, validate the first element
            if len(value) > 0:
                value = value[0]
            else:
                return False  # Empty tuple is invalid
        
        # Handle other non-numeric types
        if not isinstance(value, (int, float)):
            try:
                value = int(value)
            except (ValueError, TypeError):
                return False  # Cannot convert to number
        
        if min_val is not None and value < min_val:
            return False
        if max_val is not None and value > max_val:
            return False
        
        return True
    
    def validate_input(self, input_str: str, constraints: str) -> bool:
        """Validate if input satisfies the constraints"""
        bounds = self.parse_constraint(constraints)
        input_values = self.extract_input_value(input_str)
        
        if not bounds or not input_values:
            return True  # If we can't parse, assume valid
        
        for var_name, (min_val, max_val) in bounds.items():
            if var_name in input_values:
                value = input_values[var_name]
                if not self.validate_value(value, (min_val, max_val)):
                    return False
        
        return True
    
    def validate_output(self, output_str: str, constraints: str) -> bool:
        """Validate if output satisfies the constraints"""
        bounds = self.parse_constraint(constraints)
        output_value = self.extract_value(output_str)
        
        if not bounds or output_value is None:
            return True  # If we can't parse, assume valid
        
        # Check output range constraints
        if '<output>' in bounds:
            # Handle tuple output (common in main functions)
            if isinstance(output_value, tuple):
                # For tuple output, validate the first element
                if len(output_value) > 0:
                    output_value = output_value[0]
                else:
                    return False  # Empty tuple is invalid
            
            if not self.validate_value(output_value, bounds['<output>']):
                return False
        
        # Check output equals constraint
        if '<output>_equals' in bounds:
            expected_value = bounds['<output>_equals']
            if str(output_value) != str(expected_value):
                return False
        
        # Check output not equals constraint
        if '<output>_not_equals' in bounds:
            not_equal_val = bounds['<output>_not_equals']
            if output_value == not_equal_val:
                return False
        
        if '<output>_not_equals_str' in bounds:
            not_equal_str = bounds['<output>_not_equals_str']
            if str(output_value) == str(not_equal_str):
                return False
        
        # Check output type constraint
        if '<output>_type' in bounds:
            expected_type = bounds['<output>_type']
            if expected_type == 'int' and not isinstance(output_value, int):
                return False
            elif expected_type == 'str' and not isinstance(output_value, str):
                return False
            elif expected_type == 'bool' and not isinstance(output_value, bool):
                return False
            elif expected_type == 'list' and not isinstance(output_value, list):
                return False
        
        # Check output boolean constraint
        if '<output>_boolean' in bounds:
            expected_bool = bounds['<output>_boolean']
            if expected_bool == 'True' and output_value is not True:
                return False
            elif expected_bool == 'False' and output_value is not False:
                return False
        
        # Check output length constraint
        if '<output>_max_length' in bounds:
            max_length = bounds['<output>_max_length']
            if isinstance(output_value, (list, str)) and len(output_value) > max_length:
                return False
        
        return True


class PythonExecutor:
    """Execute Python code and get actual output"""
    
    def __init__(self):
        self.error_dir = "../../logs/no_testcases"
        os.makedirs(self.error_dir, exist_ok=True)
    
    def execute_python_file(self, py_file: str, input_value: Any, entry_func: str) -> Tuple[bool, Any]:
        """Execute Python file with given input and return actual output"""
        try:
            # Create a temporary Python script to execute the function
            temp_script = f"""
import sys
import traceback

# Add the directory containing the Python file to sys.path
import os
sys.path.insert(0, os.path.dirname(r'{py_file}'))

# Import the module
module_name = os.path.splitext(os.path.basename(r'{py_file}'))[0]
try:
    module = __import__(module_name)
except Exception as e:
    print(f"Import error: {{e}}")
    sys.exit(1)

# Find the main function (function starting with 'main_')
main_func = None
for attr_name in dir(module):
    if attr_name.startswith('main_'):
        main_func = getattr(module, attr_name)
        break

if main_func is None:
    print("No main function found")
    sys.exit(1)

# Execute the main function with input
try:
    result = main_func({input_value})
    print("SUCCESS")
    print(result)
except Exception as e:
    print(f"Execution error: {{e}}")
    traceback.print_exc()
    sys.exit(1)
"""
            
            # Write temporary script
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as temp_file:
                temp_file.write(temp_script)
                temp_script_path = temp_file.name
            
            try:
                # Execute the script
                result = subprocess.run(
                    ['python3', temp_script_path],
                    capture_output=True,
                    text=True,
                    timeout=10  # 10 seconds timeout
                )
                
                # Parse output
                if result.returncode == 0:
                    lines = result.stdout.strip().split('\n')
                    if len(lines) >= 2 and lines[0] == 'SUCCESS':
                        output_str = lines[1]
                        # Try to parse the output
                        try:
                            output_value = ast.literal_eval(output_str)
                            return True, output_value
                        except:
                            return True, output_str
                    else:
                        return False, f"Unexpected output format: {result.stdout}"
                else:
                    return False, f"Execution failed: {result.stderr}"
                    
            finally:
                # Clean up temporary file
                if os.path.exists(temp_script_path):
                    os.unlink(temp_script_path)
                    
        except subprocess.TimeoutExpired:
            return False, "Execution timeout"
        except Exception as e:
            return False, f"Execution error: {e}"
    
    def move_to_error(self, comp_dir: str, reason: str):
        """Move directory to error folder"""
        try:
            dir_name = os.path.basename(comp_dir)
            error_path = os.path.join(self.error_dir, dir_name)
            
            # If directory already exists, add timestamp
            if os.path.exists(error_path):
                timestamp = int(time.time())
                error_path = f"{error_path}_{timestamp}"
            
            # Move the directory
            shutil.move(comp_dir, error_path)
            
            # Create or append to error log (don't overwrite existing error_reason.txt)
            error_log_path = os.path.join(error_path, "move_reason.txt")
            with open(error_log_path, 'w') as f:
                f.write(f"Directory moved to error folder\n")
                f.write(f"Reason: {reason}\n")
                f.write(f"\nNote: Check error_reason.txt for detailed execution error analysis.\n")
            
            print(f"Moved empty directory to: {error_path}")
            
        except Exception as e:
            print(f"Error moving directory: {e}")


class RootFunctionAnalyzer:
    """Analyze root function constraints from Python file"""
    
    def __init__(self):
        self.root_function = None
        self.input_constraints = {}
        self.output_constraints = {}
    
    def find_root_function(self, py_file: str) -> Optional[str]:
        """Find the root function (first function called in main)"""
        try:
            with open(py_file, 'r', encoding='utf-8') as f:
                code = f.read()
            
            tree = ast.parse(code)
            
            # Find main function and its first function call
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef) and node.name.startswith('main_'):
                    # Look for the first function call in main
                    for stmt in node.body:
                        if isinstance(stmt, ast.AnnAssign) and stmt.value and isinstance(stmt.value, ast.Call):
                            if isinstance(stmt.value.func, ast.Name):
                                return stmt.value.func.id
            
            return None
        except Exception as e:
            print(f"Error finding root function: {e}")
            return None
    
    def extract_constraints_from_comments(self, code: str, func_name: str) -> Tuple[str, str]:
        """Extract input and output constraints from function comments"""
        input_constraint = ""
        output_constraint = ""
        
        lines = code.split('\n')
        in_target_function = False
        
        for line in lines:
            line = line.strip()
            
            # Check for function definition
            if line.startswith(f'def {func_name}('):
                in_target_function = True
                continue
            elif line.startswith('def ') and in_target_function:
                # We've moved to the next function
                break
            
            # Check for constraint comments within the target function
            if in_target_function and line.startswith('#'):
                comment_content = line[1:].strip()
                if 'input:' in comment_content:
                    input_constraint = comment_content.split('input:', 1)[1].strip()
                elif 'output:' in comment_content:
                    output_constraint = comment_content.split('output:', 1)[1].strip()
                elif re.search(r'[a-zA-Z_]\w*\s*[<>=]', comment_content) and not comment_content.startswith('input:') and not comment_content.startswith('output:'):
                    # This is a constraint comment without input:/output: prefix
                    input_constraint = comment_content
        
        return input_constraint, output_constraint
    
    def analyze_python_file(self, py_file: str) -> Tuple[Optional[str], str, str]:
        """Analyze Python file to find root function and its constraints"""
        try:
            with open(py_file, 'r', encoding='utf-8') as f:
                code = f.read()
            
            # Find root function
            root_func = self.find_root_function(py_file)
            if not root_func:
                return None, "", ""
            
            # Extract constraints for root function
            input_constraint, output_constraint = self.extract_constraints_from_comments(code, root_func)
            
            return root_func, input_constraint, output_constraint
            
        except Exception as e:
            print(f"Error analyzing Python file {py_file}: {e}")
            return None, "", ""


class SimpleTestCaseFilter:
    """Simplified testcase filter that only validates root function IO constraints"""
    
    def __init__(self):
        self.validator = SimpleConstraintValidator()
        self.analyzer = RootFunctionAnalyzer()
        self.executor = PythonExecutor()
    
    def load_jsonl_file(self, file_path: str) -> List[Dict[str, Any]]:
        """Load and parse JSONL file"""
        data = []
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if line:
                        data.append(json.loads(line))
        except Exception as e:
            print(f"Error loading file {file_path}: {e}")
        return data
    
    def filter_io_samples_by_constraints(self, io_samples: List[Dict[str, str]], 
                                       input_constraint: str, output_constraint: str,
                                       py_file: str, root_func: str, output_py_file: str = None) -> List[Dict[str, str]]:
        """Filter IO samples by validating constraints and actual execution"""
        if not io_samples:
            return io_samples
        
        print(f"Total samples: {len(io_samples)}")
        
        # Step 0: Remove duplicates based on input values
        unique_samples = {}
        for sample in io_samples:
            input_str = sample.get('input', '')
            output_str = sample.get('output', '')
            
            # Extract input value for deduplication
            input_values = self.validator.extract_input_value(input_str)
            if input_values:
                input_value = list(input_values.values())[0]
                # Use input value as key, keep the first occurrence
                if input_value not in unique_samples:
                    unique_samples[input_value] = {
                        'input': input_str,
                        'output': output_str,
                        'original_sample': sample
                    }
        
        print(f"After deduplication: {len(unique_samples)} unique input values")
        
        filtered_samples = []
        execution_errors = []  # Track execution errors
        
        # Add progress bar for sample processing
        for i, (input_value, sample_info) in enumerate(tqdm(unique_samples.items(), desc="Processing samples", unit="sample")):
            input_str = sample_info['input']
            original_output = sample_info['output']
            
            # Step 1: Validate input constraints
            if input_constraint and not self.validator.validate_input(input_str, input_constraint):
                print(f"Sample {i+1}: ✗ input='{input_str}' violates input constraint '{input_constraint}'")
                continue
            
            # Step 2: Validate original output constraints (from JSONL)
            if output_constraint and not self.validator.validate_output(original_output, output_constraint):
                print(f"Sample {i+1}: ✗ output='{original_output}' violates output constraint '{output_constraint}'")
                continue
            
            # Step 3: Execute the Python file to get actual output
            success, actual_output = self.executor.execute_python_file(py_file, input_value, root_func)
            
            if not success:
                error_info = {
                    'sample_index': i + 1,
                    'input': input_str,
                    'original_output': original_output,
                    'error': actual_output
                }
                execution_errors.append(error_info)
                print(f"Sample {i+1}: ✗ input='{input_str}' -> execution failed: {actual_output}")
                continue
            
            # Step 4: Create new sample with actual output
            new_sample = {
                'input': input_str,
                'output': str(actual_output)
            }
            filtered_samples.append(new_sample)
            print(f"Sample {i+1}: ✓ input='{input_str}' -> output='{actual_output}'")
        
        print(f"Filtered samples: {len(filtered_samples)}")
        
        # Save execution errors to file in output directory
        self._save_execution_errors(execution_errors, output_py_file or py_file)
        
        return filtered_samples
    
    def _save_execution_errors(self, execution_errors: List[Dict], py_file: str):
        """Save execution errors to error_reason.txt in the output directory"""
        try:
            # Get the directory containing the Python file (output directory)
            py_dir = Path(py_file).parent
            error_file = py_dir / "error_reason.txt"
            
            with open(error_file, 'w', encoding='utf-8') as f:
                f.write("Execution Error Analysis Report\n")
                f.write("=" * 50 + "\n\n")
                
                if execution_errors:
                    f.write(f"Found {len(execution_errors)} testcases that passed IO constraints but failed execution:\n\n")
                    
                    for error in execution_errors:
                        f.write(f"Sample {error['sample_index']}:\n")
                        f.write(f"  Input: {error['input']}\n")
                        f.write(f"  Original Output: {error['original_output']}\n")
                        f.write(f"  Execution Error: {error['error']}\n")
                        f.write("-" * 30 + "\n")
                    
                    f.write(f"\nTotal execution errors: {len(execution_errors)}\n")
                else:
                    f.write("No execution errors found.\n")
                    f.write("All testcases that passed IO constraints also passed execution successfully.\n")
            
            print(f"Execution error report saved to: {error_file}")
            
        except Exception as e:
            print(f"Error saving execution error report: {e}")
    
    def process_composition_testcase(self, jsonl_file: str, py_file: str, output_file: str) -> bool:
        """Process a composition testcase with simplified validation"""
        print(f"Processing composition testcase:")
        print(f"  JSONL file: {jsonl_file}")
        print(f"  Python file: {py_file}")
        
        # Load JSONL data
        jsonl_data = self.load_jsonl_file(jsonl_file)
        if not jsonl_data:
            print("No data found in JSONL file")
            return False
        
        # Analyze Python file to find root function and constraints
        root_func, input_constraint, output_constraint = self.analyzer.analyze_python_file(py_file)
        if not root_func:
            print("Could not find root function")
            return False
        
        print(f"Root function: {root_func}")
        print(f"Input constraint: {input_constraint}")
        print(f"Output constraint: {output_constraint}")
        
        # MODIFIED CODE - Collect all io_samples from all functions in compositions.jsonl
        all_io_samples = []
        total_original_samples = 0
        
        for item in jsonl_data:
            if 'io_sample' in item and item['io_sample']:
                all_io_samples.extend(item['io_sample'])
                total_original_samples += len(item['io_sample'])
        
        if not all_io_samples:
            print("No io_samples found in compositions.jsonl")
            return False
        
        print(f"Total io_samples collected from all functions: {len(all_io_samples)}")
        
        # Get output Python file path for error reporting
        output_path = Path(output_file)
        output_py_file = output_path.parent / Path(py_file).name
        
        # MODIFIED CODE - Filter IO samples by constraints and execution
        filtered_io_samples = self.filter_io_samples_by_constraints(
            all_io_samples,
            input_constraint, output_constraint,
            py_file, root_func, str(output_py_file)
        )
        
        # Check if we have any samples left
        if not filtered_io_samples:
            print("No valid testcases found after filtering")
            return False
        
        # Create new testcase data with root function as entry_point
        testcase_data = {
            'root_func': root_func,
            'io_sample': filtered_io_samples
        }
        
        # Ensure output directory exists
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        # Save filtered testcase data
        try:
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(json.dumps(testcase_data, ensure_ascii=False) + '\n')
            
            print(f"Filtered testcase saved to: {output_file}")
            
            # MODIFIED CODE - Print statistics with deduplication info
            print(f"Final testcases: {len(filtered_io_samples)}/{total_original_samples} "
                  f"({len(filtered_io_samples)/total_original_samples*100:.1f}% kept after deduplication and filtering)")
            
            # Clean up compositions.jsonl in output directory (not the original input file)
            output_compositions_file = output_path.parent / "compositions.jsonl"
            if output_compositions_file.exists():
                self._cleanup_compositions_jsonl(str(output_compositions_file))
            
            return True
            
        except Exception as e:
            print(f"Error saving file {output_file}: {e}")
            return False
    
    def _cleanup_compositions_jsonl(self, jsonl_file: str):
        """Remove io_sample fields from compositions.jsonl to reduce file size"""
        try:
            # Load original data
            jsonl_data = self.load_jsonl_file(jsonl_file)
            if not jsonl_data:
                return
            
            # Create backup of original file
            backup_file = jsonl_file + '.backup'
            import shutil
            shutil.copy2(jsonl_file, backup_file)
            print(f"Created backup: {backup_file}")
            
            # Remove io_sample fields from all entries
            cleaned_data = []
            for item in jsonl_data:
                cleaned_item = item.copy()
                if 'io_sample' in cleaned_item:
                    del cleaned_item['io_sample']
                cleaned_data.append(cleaned_item)
            
            # Write cleaned data back to file
            with open(jsonl_file, 'w', encoding='utf-8') as f:
                for item in cleaned_data:
                    f.write(json.dumps(item, ensure_ascii=False) + '\n')
            
            print(f"Cleaned compositions.jsonl: removed io_sample fields from {len(jsonl_data)} entries")
            
        except Exception as e:
            print(f"Error cleaning up compositions.jsonl: {e}")
            # Try to restore from backup if cleanup failed
            if os.path.exists(backup_file):
                try:
                    shutil.copy2(backup_file, jsonl_file)
                    print("Restored original file from backup")
                except Exception as restore_error:
                    print(f"Error restoring from backup: {restore_error}")
    
    def process_single_testcase(self, testcase_dir: Path, output_dir: Path) -> Tuple[str, bool, str]:
        """Process a single testcase directory - designed for parallel execution"""
        try:
            testcase_name = testcase_dir.name
            jsonl_file = next(testcase_dir.glob('*.jsonl'))
            py_file = next(testcase_dir.glob('*.py'))
            
            # Create output subdirectory
            output_subdir = output_dir / testcase_name
            output_subdir.mkdir(parents=True, exist_ok=True)
            
            # Copy all files from original directory to output directory
            for item in testcase_dir.iterdir():
                if item.is_file():
                    dst_file = output_subdir / item.name
                    shutil.copy2(item, dst_file)
            
            # Create testcase.jsonl file
            output_file = output_subdir / "testcase.jsonl"
            
            # Process the testcase
            success = self.process_composition_testcase(str(jsonl_file), str(py_file), str(output_file))
            
            # If no testcases were generated, move to error directory
            if not success:
                self.executor.move_to_error(str(output_subdir), "No valid testcases after filtering")
                return testcase_name, False, "No valid testcases after filtering"
            else:
                return testcase_name, True, "Successfully processed"
                
        except Exception as e:
            error_msg = f"Error processing {testcase_dir.name}: {str(e)}"
            return testcase_dir.name, False, error_msg

    def process_directory(self, input_dir: str, output_dir: str, max_workers: int = None) -> None:
        """Process all composition testcases in a directory with parallel processing"""
        input_path = Path(input_dir)
        output_path = Path(output_dir)
        
        if not input_path.exists():
            print(f"Input directory does not exist: {input_dir}")
            return
        
        # Create output directory if it doesn't exist
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Find all directories with both JSONL and Python files
        testcase_dirs = []
        for item in input_path.iterdir():
            if item.is_dir():
                jsonl_files = list(item.glob('*.jsonl'))
                py_files = list(item.glob('*.py'))
                if jsonl_files and py_files:
                    testcase_dirs.append(item)
        
        if not testcase_dirs:
            print(f"No composition testcases found in {input_dir}")
            return
        
        print(f"Found {len(testcase_dirs)} composition testcases to process")
        
        # Determine number of workers
        if max_workers is None:
            max_workers = min(mp.cpu_count(), len(testcase_dirs))
        
        print(f"Using {max_workers} parallel workers")
        
        # Process testcases in parallel
        if max_workers > 1:
            self._process_directory_parallel(testcase_dirs, output_path, max_workers)
        else:
            self._process_directory_serial(testcase_dirs, output_path)
    
    def _process_directory_parallel(self, testcase_dirs: List[Path], output_path: Path, max_workers: int):
        """Process testcases using multiprocessing pool"""
        # Create a partial function with fixed output_dir parameter
        process_func = partial(self.process_single_testcase, output_dir=output_path)
        
        # Use multiprocessing pool
        with mp.Pool(processes=max_workers) as pool:
            # Use imap to get results as they complete with progress bar
            results = list(tqdm(
                pool.imap(process_func, testcase_dirs),
                total=len(testcase_dirs),
                desc="Processing testcases",
                unit="testcase"
            ))
        
        # Process results
        successful = 0
        failed = 0
        
        for testcase_name, success, message in results:
            if success:
                successful += 1
                print(f"✓ {testcase_name}: {message}")
            else:
                failed += 1
                print(f"✗ {testcase_name}: {message}")
        
        print(f"\nProcessing completed:")
        print(f"  Successful: {successful}")
        print(f"  Failed: {failed}")
        print(f"  Total: {len(testcase_dirs)}")
    
    def _process_directory_serial(self, testcase_dirs: List[Path], output_path: Path):
        """Process testcases serially (original method)"""
        for testcase_dir in tqdm(testcase_dirs, desc="Processing testcases", unit="testcase"):
            testcase_name, success, message = self.process_single_testcase(testcase_dir, output_path)
            
            if success:
                print(f"✓ {testcase_name}: {message}")
            else:
                print(f"✗ {testcase_name}: {message}")
            
            print("-" * 50)


def main():
    parser = argparse.ArgumentParser(description='Parallel testcase filter for DafnyAutoSpec')
    parser.add_argument('--input-dir', type=str, 
                       required=True,
                       help='Input directory containing testcases')
    parser.add_argument('--output-dir', type=str,
                       required=True,
                       help='Output directory for filtered testcases')
    parser.add_argument('--workers', type=int, default=os.cpu_count() - 1,
                       help='Number of parallel workers (default: min(CPU cores, testcase count))')
    parser.add_argument('--serial', action='store_true',
                       help='Force serial processing (disable parallel processing)')
    
    args = parser.parse_args()

    # Set up logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler('../../logs/testcase_filter.log'),
            logging.StreamHandler()
        ]
    )
    
    print(f"Starting testcase filtering:")
    print(f"  Input directory: {args.input_dir}")
    print(f"  Output directory: {args.output_dir}")
    print(f"  Workers: {args.workers if not args.serial else 1}")
    print(f"  Mode: {'Serial' if args.serial else 'Parallel'}")
    print("-" * 60)
    
    start_time = time.time()
    
    filter_tool = SimpleTestCaseFilter()
    
    if args.serial:
        # Force serial processing
        filter_tool.process_directory(args.input_dir, args.output_dir, max_workers=1)
    else:
        # Use parallel processing
        filter_tool.process_directory(args.input_dir, args.output_dir, max_workers=args.workers)
    
    end_time = time.time()
    elapsed_time = end_time - start_time
    
    print(f"\nTotal processing time: {elapsed_time:.2f} seconds ({elapsed_time/60:.2f} minutes)")


if __name__ == "__main__":
    main() 