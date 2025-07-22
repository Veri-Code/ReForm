#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Simple constraint analyzer for function compositions.
Analyzes input/output constraints and propagates them through function calls.
"""

import re
import ast
import json
import os
import shutil
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime
import logging
import sys
from tqdm import tqdm

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Setup logging
def setup_logging(log_file: str = "../../logs/constraint_analysis.log"):
    """Setup logging configuration"""
    # Ensure logs directory exists
    log_dir = os.path.dirname(log_file)
    os.makedirs(log_dir, exist_ok=True)
    
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file, encoding='utf-8'),
            logging.StreamHandler(sys.stdout)
        ]
    )
    return logging.getLogger(__name__)

logger = setup_logging()

@dataclass
class Range:
    """Represents a range constraint"""
    lower: Optional[int] = None
    upper: Optional[int] = None
    var_name: str = 'x'
    
    def __str__(self) -> str:
        if self.lower is not None and self.upper is not None:
            return f"{self.lower} <= {self.var_name} <= {self.upper}"
        elif self.lower is not None:
            return f"{self.var_name} >= {self.lower}"
        elif self.upper is not None:
            return f"{self.var_name} <= {self.upper}"
        return "unconstrained"
    
    def output_str(self) -> str:
        """String representation for output constraints"""
        if self.lower is not None and self.upper is not None:
            return f"{self.lower} <= <output> <= {self.upper}"
        elif self.lower is not None:
            return f"<output> >= {self.lower}"
        elif self.upper is not None:
            return f"<output> <= {self.upper}"
        return "unconstrained"
    
    def intersection(self, other: 'Range') -> 'Range':
        """Get intersection of two ranges"""
        new_lower = max(self.lower, other.lower) if self.lower is not None and other.lower is not None else \
                   (self.lower if self.lower is not None else other.lower)
        new_upper = min(self.upper, other.upper) if self.upper is not None and other.upper is not None else \
                   (self.upper if self.upper is not None else other.upper)
        return Range(new_lower, new_upper, self.var_name)

@dataclass
class FunctionConstraint:
    """Represents function constraints"""
    name: str
    input_range: Range
    output_range: Range
    code: str
    entry_point: str

class SimpleConstraintAnalyzer:
    """Simple constraint analyzer for function compositions"""
    
    def __init__(self, error_dir: str = None, constraint_check_dir: str = None):
        self.function_constraints: Dict[str, FunctionConstraint] = {}
        self.composition_graph: Dict[str, List[str]] = {}
        self.data_flow: Dict[str, str] = {}
        self.variable_usage: Dict[str, str] = {}
        self.adjusted_constraints: Dict[str, Dict[str, Range]] = {}
        
        # Set default paths if not provided
        if error_dir is None:
            raise ValueError("error_dir is required")
        if constraint_check_dir is None:
            raise ValueError("constraint_check_dir is required")
        
        self.error_dir = error_dir
        self.constraint_check_dir = constraint_check_dir
        os.makedirs(self.error_dir, exist_ok=True)
        os.makedirs(self.constraint_check_dir, exist_ok=True)
    
    def parse_constraint(self, constraint_str: str) -> Range:
        """Parse constraint string to Range object"""
        if not constraint_str or constraint_str.strip() == "":
            return Range()
        
        constraint = constraint_str.strip()
        
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
        
        # Extract variable name - look for the variable that appears in comparisons
        var_pattern = r'[a-zA-Z_]\w*'
        var_matches = re.findall(var_pattern, constraint)
        
        var_name = 'x'  # default
        for var in var_matches:
            # Skip common keywords
            if var.lower() not in ['and', 'or', 'not', 'true', 'false', 'inf', 'nan']:
                # Check if this variable appears in comparison operators
                if re.search(rf'\b{re.escape(var)}\s*[<>=]', constraint) or \
                   re.search(rf'[<>=]\s*{re.escape(var)}\b', constraint):
                    var_name = var
                    break
        
        # Normalize constraint by replacing the variable name with 'x'
        normalized = re.sub(rf'\b{re.escape(var_name)}\b', 'x', constraint)
        
        # Parse bounds
        lower = None
        upper = None
        
        # Pattern: number <= x <= number
        full_match = re.search(r'(-?\d+)\s*<=\s*x\s*<=\s*(-?\d+)', normalized)
        if full_match:
            lower = int(full_match.group(1))
            upper = int(full_match.group(2))
        else:
            # Pattern: x <= number
            upper_match = re.search(r'x\s*<=\s*(-?\d+)', normalized)
            if upper_match:
                upper = int(upper_match.group(1))
            
            # Pattern: number <= x
            lower_match = re.search(r'(-?\d+)\s*<=\s*x', normalized)
            if lower_match:
                lower = int(lower_match.group(1))
            
            # Pattern: x >= number
            lower_match2 = re.search(r'x\s*>=\s*(-?\d+)', normalized)
            if lower_match2:
                lower = int(lower_match2.group(1))
        
        return Range(lower, upper, var_name)
    
    def analyze_function_output(self, code: str) -> Range:
        """Analyze function code to determine output constraints"""
        try:
            tree = ast.parse(code)
            
            # Look for return statements and analyze their values
            for node in ast.walk(tree):
                if isinstance(node, ast.Return) and node.value:
                    # Analyze return value
                    if isinstance(node.value, ast.Name):
                        # Return variable - check if it has constraints
                        var_name = node.value.id
                        # Look for variable assignments in the function
                        for stmt in ast.walk(tree):
                            if isinstance(stmt, ast.Assign):
                                for target in stmt.targets:
                                    if isinstance(target, ast.Name) and target.id == var_name:
                                        # Analyze the assignment value
                                        return self._analyze_expression_constraints(stmt.value)
                    else:
                        # Return expression - analyze directly
                        return self._analyze_expression_constraints(node.value)
            
            # If no specific output constraints found, return unconstrained
            return Range()
            
        except Exception as e:
            logger.warning(f"Error analyzing function output: {e}")
            return Range()
    
    def _analyze_expression_constraints(self, expr: ast.expr) -> Range:
        """Analyze expression to determine constraints"""
        if isinstance(expr, ast.Constant):
            if isinstance(expr.value, (int, float)):
                return Range(lower=expr.value, upper=expr.value)
        elif isinstance(expr, ast.BinOp):
            # Handle binary operations
            left_constraints = self._analyze_expression_constraints(expr.left)
            right_constraints = self._analyze_expression_constraints(expr.right)
            
            if isinstance(expr.op, ast.Add):
                # Addition: result >= left.lower + right.lower, result <= left.upper + right.upper
                new_lower = None
                new_upper = None
                if left_constraints.lower is not None and right_constraints.lower is not None:
                    new_lower = left_constraints.lower + right_constraints.lower
                if left_constraints.upper is not None and right_constraints.upper is not None:
                    new_upper = left_constraints.upper + right_constraints.upper
                return Range(new_lower, new_upper)
            elif isinstance(expr.op, ast.Mult):
                # Multiplication: more complex, return unconstrained for now
                return Range()
        
        return Range()
    
    def load_function_constraints(self, jsonl_path: str):
        """Load function constraints from JSONL file"""
        with open(jsonl_path, 'r') as f:
            for line in f:
                data = json.loads(line)
                
                # Parse input constraint
                input_constraint = data.get('constraints', '')
                input_range = self.parse_constraint(input_constraint)
                
                # For now, set output range as unconstrained
                # We'll analyze it later based on function composition
                output_range = Range()
                
                self.function_constraints[data['entry_point']] = FunctionConstraint(
                    name=data['name'],
                    input_range=input_range,
                    output_range=output_range,
                    code=data['code'],
                    entry_point=data['entry_point']
                )
    
    def analyze_main_function(self, main_node: ast.FunctionDef):
        """Analyze main function to build call graph and data flow"""
        called_funcs = []
        data_flow = {}
        variable_usage = {}
        
        print(f"Analyzing main function: {main_node.name}")
        
        # First pass: find function calls and their outputs
        for stmt in main_node.body:
            if isinstance(stmt, ast.AnnAssign) and stmt.value and isinstance(stmt.value, ast.Call):
                if isinstance(stmt.target, ast.Name) and isinstance(stmt.value.func, ast.Name):
                    target_var = stmt.target.id
                    func_name = stmt.value.func.id
                    called_funcs.append(func_name)
                    data_flow[target_var] = func_name
                    print(f"  {target_var} = {func_name}()")
        
        # Second pass: find functions that use variables as arguments
        for stmt in main_node.body:
            if isinstance(stmt, ast.AnnAssign) and stmt.value and isinstance(stmt.value, ast.Call):
                if isinstance(stmt.value.func, ast.Name):
                    func_name = stmt.value.func.id
                    for arg in stmt.value.args:
                        if isinstance(arg, ast.Name) and arg.id in data_flow:
                            variable_usage[func_name] = arg.id
                            print(f"  {func_name} uses {arg.id} (from {data_flow[arg.id]})")
        
        self.composition_graph[main_node.name] = list(set(called_funcs))
        self.data_flow = data_flow
        self.variable_usage = variable_usage
    
    def has_conflict(self, range1: Range, range2: Range) -> bool:
        """Check if two ranges have a conflict (no intersection)"""
        # If either range is unconstrained, no conflict
        if range1.lower is None and range1.upper is None:
            return False
        if range2.lower is None and range2.upper is None:
            return False
        
        # Check for conflicts
        if range1.lower is not None and range2.upper is not None and range1.lower > range2.upper:
            return True
        if range1.upper is not None and range2.lower is not None and range1.upper < range2.lower:
            return True
        
        return False
    
    def propagate_constraints(self) -> bool:
        """Propagate constraints through the call graph"""
        has_conflicts = False
        
        # Get the actual functions used in this composition
        used_functions = set()
        for called_funcs in self.composition_graph.values():
            used_functions.update(called_funcs)
        
        # For each main function
        for main_func, called_funcs in self.composition_graph.items():
            if main_func not in self.adjusted_constraints:
                self.adjusted_constraints[main_func] = {}
            
            # Find functions whose outputs are used by other functions
            for var_name, producer_func in self.data_flow.items():
                # Only process functions that are actually used in this composition
                if producer_func not in used_functions:
                    continue
                    
                producer_constraint = self.function_constraints.get(producer_func)
                if not producer_constraint:
                    continue
                
                # Find all consumers of this variable
                consumers = []
                for func_name, used_var in self.variable_usage.items():
                    if used_var == var_name and func_name in used_functions:
                        consumers.append(func_name)
                
                # Check for conflicts between all pairs of consumers
                if len(consumers) > 1:
                    logger.info(f"Checking conflicts between {len(consumers)} consumers of {producer_func}: {consumers}")
                    
                    for i in range(len(consumers)):
                        for j in range(i + 1, len(consumers)):
                            consumer1 = self.function_constraints.get(consumers[i])
                            consumer2 = self.function_constraints.get(consumers[j])
                            
                            if consumer1 and consumer2:
                                if self.has_conflict(consumer1.input_range, consumer2.input_range):
                                    logger.error(f"CONFLICT DETECTED: {consumers[i]} and {consumers[j]} have conflicting input constraints")
                                    logger.error(f"  {consumers[i]}: {consumer1.input_range}")
                                    logger.error(f"  {consumers[j]}: {consumer2.input_range}")
                                    has_conflicts = True
                
                # Calculate required output range by intersecting all consumer constraints
                required_output = None
                consumer_constraints = []
                
                for consumer_func in consumers:
                    consumer_constraint = self.function_constraints.get(consumer_func)
                    if consumer_constraint:
                        consumer_constraints.append(consumer_constraint.input_range)
                        if required_output is None:
                            required_output = consumer_constraint.input_range
                        else:
                            required_output = required_output.intersection(consumer_constraint.input_range)
                
                # Log the intersection process
                if len(consumer_constraints) > 1:
                    logger.info(f"Intersecting constraints for {producer_func} output:")
                    for i, constraint in enumerate(consumer_constraints):
                        logger.info(f"  Consumer {i+1}: {constraint}")
                    logger.info(f"  Result: {required_output}")
                
                # Check if intersection is empty (conflict)
                if required_output and required_output.lower is not None and required_output.upper is not None:
                    if required_output.lower > required_output.upper:
                        logger.error(f"CONFLICT DETECTED: Empty intersection for {producer_func} output")
                        logger.error(f"  Required output: {required_output}")
                        logger.error(f"  Consumer constraints: {consumer_constraints}")
                        has_conflicts = True
                
                # Update producer's output range
                if required_output and required_output != producer_constraint.output_range:
                    if producer_func not in self.adjusted_constraints[main_func]:
                        self.adjusted_constraints[main_func][producer_func] = {}
                    self.adjusted_constraints[main_func][producer_func]['output'] = required_output
                    
                    logger.info(f"Adjusted {producer_func} output: {producer_constraint.output_range} -> {required_output}")
                    producer_constraint.output_range = required_output
        
        return has_conflicts
    
    def update_code_constraints(self, code: str, func_name: str) -> str:
        """Update constraint comments in code"""
        if func_name not in self.function_constraints:
            return code
        
        constraint = self.function_constraints[func_name]
        lines = code.split('\n')
        updated_lines = []
        
        i = 0
        while i < len(lines):
            line = lines[i]
            
            # Check if this is a function definition
            if line.strip().startswith(f'def {func_name}('):
                updated_lines.append(line)
                i += 1
                
                # Find the original constraint comment (if any)
                original_constraint = None
                while i < len(lines) and lines[i].strip().startswith('#'):
                    comment_content = lines[i].strip()[1:].strip()
                    if re.search(r'[a-zA-Z_]\w*\s*[<>=]', comment_content) and not comment_content.startswith('input:') and not comment_content.startswith('output:'):
                        original_constraint = comment_content
                        break
                    i += 1
                
                # Add original constraint if found
                if original_constraint:
                    updated_lines.append(f"    # original: {original_constraint}")
                
                # Add input constraint
                updated_lines.append(f"    # input: {constraint.input_range}")
                
                # Add output constraint
                updated_lines.append(f"    # output: {constraint.output_range.output_str()}")
                
                # Skip any existing constraint comments
                while i < len(lines) and lines[i].strip().startswith('#'):
                    comment_content = lines[i].strip()[1:].strip()
                    if re.search(r'[a-zA-Z_]\w*\s*[<>=]', comment_content) or comment_content.startswith('input:') or comment_content.startswith('output:'):
                        i += 1  # Skip this comment
                    else:
                        updated_lines.append(lines[i])  # Keep other comments
                        i += 1
            else:
                updated_lines.append(line)
                i += 1
        
        return '\n'.join(updated_lines)
    
    def process_composition(self, comp_dir: str) -> bool:
        """Process a single composition directory"""
        try:
            dir_name = os.path.basename(comp_dir)
            py_file = os.path.join(comp_dir, f"{dir_name}.py")
            jsonl_file = os.path.join(comp_dir, "compositions.jsonl")
            
            if not (os.path.exists(py_file) and os.path.exists(jsonl_file)):
                logger.error(f"Required files not found in {comp_dir}")
                return False
            
            # Reset state for this composition
            self.function_constraints.clear()
            self.composition_graph.clear()
            self.data_flow.clear()
            self.variable_usage.clear()
            self.adjusted_constraints.clear()
            
            # Load function constraints
            self.load_function_constraints(jsonl_file)
            
            # Parse main function
            with open(py_file, 'r') as f:
                content = f.read()
            tree = ast.parse(content)
            
            # Find main function
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef) and node.name.startswith('main_'):
                    self.analyze_main_function(node)
                    break
            
            # Propagate constraints
            has_conflicts = self.propagate_constraints()
            
            if has_conflicts:
                self._move_to_error(comp_dir)
                return False
            
            # Copy and update files
            target_dir = os.path.join(self.constraint_check_dir, dir_name)
            os.makedirs(target_dir, exist_ok=True)
            
            # Copy non-Python files
            for item in os.listdir(comp_dir):
                src_path = os.path.join(comp_dir, item)
                dst_path = os.path.join(target_dir, item)
                if os.path.isfile(src_path) and not item.endswith('.py'):
                    shutil.copy2(src_path, dst_path)
            
            # Process Python files
            for item in os.listdir(comp_dir):
                if not item.endswith('.py'):
                    continue
                
                src_path = os.path.join(comp_dir, item)
                dst_path = os.path.join(target_dir, item)
                
                with open(src_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Update constraints for each function
                tree = ast.parse(content)
                for node in ast.walk(tree):
                    if isinstance(node, ast.FunctionDef):
                        content = self.update_code_constraints(content, node.name)
                
                with open(dst_path, 'w', encoding='utf-8') as f:
                    f.write(content)
            
            # Save modification log in the target directory
            if self.adjusted_constraints:
                self._save_modification_log(target_dir)
            
            return True
            
        except Exception as e:
            logger.error(f"Error processing {comp_dir}: {e}")
            return False
    
    def _move_to_error(self, comp_dir: str):
        """Move directory to error folder and save conflict details"""
        try:
            dir_name = os.path.basename(comp_dir)
            error_path = os.path.join(self.error_dir, dir_name)
            if os.path.exists(error_path):
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                error_path = f"{error_path}_{timestamp}"
            
            # Save conflict details before moving
            conflict_log_path = os.path.join(comp_dir, "constraint_conflict.log")
            with open(conflict_log_path, 'w', encoding='utf-8') as f:
                f.write(f"Constraint Conflict Analysis - {datetime.now()}\n")
                f.write("=" * 60 + "\n\n")
                f.write(f"Directory: {dir_name}\n")
                f.write(f"Analysis time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
                
                # Log function constraints
                f.write("Function Constraints:\n")
                f.write("-" * 30 + "\n")
                for func_name, constraint in self.function_constraints.items():
                    f.write(f"{func_name}:\n")
                    f.write(f"  Input: {constraint.input_range}\n")
                    f.write(f"  Output: {constraint.output_range}\n\n")
                
                # Log composition graph
                f.write("Composition Graph:\n")
                f.write("-" * 30 + "\n")
                for main_func, called_funcs in self.composition_graph.items():
                    f.write(f"{main_func}: {called_funcs}\n")
                f.write("\n")
                
                # Log data flow
                f.write("Data Flow:\n")
                f.write("-" * 30 + "\n")
                for var, func in self.data_flow.items():
                    f.write(f"{var} <- {func}\n")
                f.write("\n")
                
                # Log variable usage
                f.write("Variable Usage:\n")
                f.write("-" * 30 + "\n")
                for func, var in self.variable_usage.items():
                    f.write(f"{func} uses {var}\n")
                f.write("\n")
                
                # Log adjusted constraints
                if self.adjusted_constraints:
                    f.write("Adjusted Constraints:\n")
                    f.write("-" * 30 + "\n")
                    for main_func, adjustments in self.adjusted_constraints.items():
                        if adjustments:
                            f.write(f"{main_func}:\n")
                            for func_name, ranges in adjustments.items():
                                if 'output' in ranges:
                                    f.write(f"  {func_name}: output -> {ranges['output']}\n")
                            f.write("\n")
            
            # Move the directory
            shutil.move(comp_dir, error_path)
            logger.info(f"Moved conflicting directory to: {error_path}")
            logger.info(f"Conflict details saved to: {os.path.join(error_path, 'constraint_conflict.log')}")
            
        except Exception as e:
            logger.error(f"Error moving directory: {e}")
    
    def _save_modification_log(self, comp_dir: str):
        """Save modification log"""
        log_path = os.path.join(comp_dir, "mod.log")
        
        # Get the actual functions used in this composition
        used_functions = set()
        for called_funcs in self.composition_graph.values():
            used_functions.update(called_funcs)
        
        with open(log_path, 'w', encoding='utf-8') as f:
            f.write(f"Constraint modifications - {datetime.now()}\n")
            f.write("=" * 50 + "\n\n")
            
            for main_func, adjustments in self.adjusted_constraints.items():
                if adjustments:
                    f.write(f"Main function: {main_func}\n")
                    f.write(f"Composition functions: {list(used_functions)}\n\n")
                    
                    # Only log adjustments for functions actually used in this composition
                    for func_name, ranges in adjustments.items():
                        if func_name in used_functions and 'output' in ranges:
                            f.write(f"  {func_name}: output -> {ranges['output']}\n")
                    f.write("\n")

def analyze_all_compositions(comp_dir: str, error_dir: str = None, constraint_check_dir: str = None):
    """Analyze all compositions in directory"""
    analyzer = SimpleConstraintAnalyzer(error_dir=error_dir, constraint_check_dir=constraint_check_dir)
    
    # Find all composition directories
    comp_dirs = []
    for root, dirs, files in os.walk(comp_dir):
        for dir_name in dirs:
            if dir_name.startswith('main_'):
                dir_path = os.path.join(root, dir_name)
                comp_dirs.append(dir_path)
    
    print(f"Found {len(comp_dirs)} composition directories")
    
    # Process each composition
    for dir_path in tqdm(comp_dirs, desc="Processing compositions"):
        logger.info(f"\nProcessing: {os.path.basename(dir_path)}")
        if analyzer.process_composition(dir_path):
            logger.info(f"✓ Success: {os.path.basename(dir_path)}")
        else:
            logger.info(f"✗ Failed: {os.path.basename(dir_path)}")

def main():
    """Main function"""

    input_dir = "../../DfyAutoSpec_wtc_chain300"
    error_dir = "../../logs/conflicts"
    output_dir = "../../DfyAutoSpec_wtc_chain300_constraint_check"
    
    analyze_all_compositions(input_dir, error_dir, output_dir)

if __name__ == "__main__":
    main() 