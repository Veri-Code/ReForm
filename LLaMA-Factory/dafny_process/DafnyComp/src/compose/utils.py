#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Combined utility functions for code processing, import management, and general utilities.
"""

import ast
import json
import os
import re
import sys
import subprocess
import tempfile
from pathlib import Path
from typing import Set, Dict, List, Tuple, Any, Optional
from tqdm import tqdm

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

try:
    from ast import unparse as ast_unparse  # Python 3.9+
except ImportError:
    import astor
    def ast_unparse(node):
        return astor.to_source(node).rstrip()

# Common standard library modules and their commonly used names (Hard Code, deprecated)
STD_LIB_IMPORTS = {
    # typing module
    'typing': [
        'List', 'Dict', 'Set', 'Tuple', 'Optional', 'Union', 'Any', 'Callable',
        'TypeVar', 'Generic', 'Iterator', 'Iterable', 'Sequence', 'Mapping',
        'Type', 'Literal', 'Final', 'Protocol', 'runtime_checkable', 'cast',
        'overload', 'TypedDict', 'NamedTuple', 'NewType', 'NoReturn', 'Self'
    ],
    
    # functools module
    'functools': [
        'wraps', 'partial', 'reduce', 'lru_cache', 'total_ordering',
        'singledispatch', 'singledispatchmethod', 'cached_property',
        'update_wrapper', 'cmp_to_key', 'partialmethod'
    ],
    
    # collections module
    'collections': [
        'defaultdict', 'Counter', 'deque', 'OrderedDict', 'ChainMap',
        'namedtuple', 'UserDict', 'UserList', 'UserString', 'abc',
        'Mapping', 'MutableMapping', 'Sequence', 'MutableSequence',
        'Set', 'MutableSet', 'MappingView', 'ItemsView', 'KeysView',
        'ValuesView'
    ],
    
    # Other common modules
    'itertools': ['chain', 'combinations', 'product', 'permutations', 'combinations_with_replacement'],
    'heapq': ['heappush', 'heappop', 'heapify', 'heapreplace', 'nlargest', 'nsmallest'],
    'bisect': ['bisect_left', 'bisect_right', 'insort_left', 'insort_right'],
    'string': ['ascii_letters', 'ascii_lowercase', 'ascii_uppercase', 'digits', 'hexdigits'],
    'operator': ['add', 'sub', 'mul', 'truediv', 'floordiv', 'mod', 'pow'],
    'math': ['sqrt', 'pow', 'exp', 'log', 'log10', 'log2', 'sin', 'cos', 'tan', 'gcd', 'lcm'],
    'random': ['randint', 'choice', 'shuffle', 'random', 'uniform', 'seed'],
    're': ['search', 'match', 'findall', 'sub', 'split', 'compile'],
    'datetime': ['datetime', 'timedelta', 'date', 'time', 'timezone'],
    'json': ['loads', 'dumps', 'load', 'dump', 'JSONEncoder'],
    'copy': ['deepcopy', 'copy']
}

# Dynamic import mapping system
class DynamicImportMapper:
    """Dynamic import mapper that uses reflection to get all available methods from modules"""
    
    def __init__(self):
        self._module_cache = {}
        self._import_cache = {}
        self._excluded_names = {
            '__builtins__', '__cached__', '__doc__', '__file__', '__loader__', 
            '__name__', '__package__', '__spec__', '__version__', '__all__',
            'builtins', 'sys', 'os', 'path', 'pathlib'
        }
    
    def get_module_attributes(self, module_name: str) -> list:
        """Get all public attributes from a module using reflection"""
        if module_name in self._module_cache:
            return self._module_cache[module_name]
        
        try:
            # Import the module
            module = __import__(module_name)
            
            # Get all attributes from the module
            attributes = []
            for attr_name in dir(module):
                # Skip private attributes and excluded names
                if not attr_name.startswith('_') and attr_name not in self._excluded_names:
                    try:
                        attr = getattr(module, attr_name)
                        # Only include callable functions/classes or constants
                        if callable(attr) or not callable(attr):
                            attributes.append(attr_name)
                    except (AttributeError, ImportError):
                        continue
            
            self._module_cache[module_name] = attributes
            return attributes
            
        except ImportError:
            # If module can't be imported, return empty list
            self._module_cache[module_name] = []
            return []
        except Exception as e:
            print(f"Warning: Error getting attributes from {module_name}: {e}")
            self._module_cache[module_name] = []
            return []
    
    def get_dynamic_imports(self, module_name: str) -> dict:
        """Get dynamic imports for a module, combining hardcoded and dynamic"""
        if module_name in self._import_cache:
            return self._import_cache[module_name]
        
        # Get hardcoded imports (fallback)
        hardcoded = STD_LIB_IMPORTS.get(module_name, [])
        
        # Get dynamic imports
        dynamic = self.get_module_attributes(module_name)
        
        # Combine and deduplicate
        combined = list(set(hardcoded + dynamic))
        combined.sort()  # Sort for consistency
        
        self._import_cache[module_name] = combined
        return combined
    
    def find_missing_imports_dynamic(self, code: str) -> dict:
        """Find missing imports using dynamic module analysis"""
        try:
            tree = ast.parse(code)
            visitor = ImportVisitor()
            visitor.visit(tree)
            
            # Find names that are used but not defined or imported
            undefined_names = visitor.used_names - visitor.defined_names - visitor.imported_names
            
            # Map undefined names to their potential modules using dynamic analysis
            missing_imports = {}
            for name in undefined_names:
                for module_name in STD_LIB_IMPORTS.keys():
                    # Check if name exists in module using dynamic analysis
                    module_attributes = self.get_dynamic_imports(module_name)
                    if name in module_attributes:
                        if module_name not in missing_imports:
                            missing_imports[module_name] = set()
                        missing_imports[module_name].add(name)
            
            return missing_imports, visitor.current_imports
            
        except SyntaxError:
            print("Warning: Could not parse code for dynamic import analysis")
            return {}, {}

# Global instance of dynamic import mapper
dynamic_mapper = DynamicImportMapper()

# Function to get dynamic imports (replaces the hardcoded STD_LIB_IMPORTS)
def get_dynamic_std_lib_imports() -> dict:
    """Get dynamic standard library imports"""
    dynamic_imports = {}
    for module_name in STD_LIB_IMPORTS.keys():
        dynamic_imports[module_name] = dynamic_mapper.get_dynamic_imports(module_name)
    return dynamic_imports

# Shared dependencies to be added
SHARED_IMPORTS = '''# Common utility functions and classes
inf = float('inf')

class ListNode:
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next

def list_node(values: list):
    if not values:
        return None
    head = ListNode(values[0])
    p = head
    for val in values[1:]:
        node = ListNode(val)
        p.next = node
        p = node
    return head

def is_same_list(p1, p2):
    if p1 is None and p2 is None:
        return True
    if not p1 or not p2:
        return False
    return p1.val == p2.val and is_same_list(p1.next, p2.next)

class TreeNode:
    def __init__(self, val=0, left=None, right=None):
        self.val = val
        self.left = left
        self.right = right

def tree_node(values: list):
    if not values:
        return None
    from collections import deque  # Import only when needed
    root = TreeNode(values[0])
    i = 1
    queue = deque()
    queue.append(root)
    while queue:
        node = queue.popleft()
        if i < len(values) and values[i] is not None:
            node.left = TreeNode(values[i])
            queue.append(node.left)
        i += 1
        if i < len(values) and values[i] is not None:
            node.right = TreeNode(values[i])
            queue.append(node.right)
        i += 1
    return root

def is_same_tree(p, q):
    if not p and not q:
        return True
    elif not p or not q:
        return False
    elif p.val != q.val:
        return False
    else:
        return is_same_tree(p.left, q.left) and is_same_tree(p.right, q.right)
'''

# ==================== JSONL Processing Functions ====================

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

# ==================== Code Analysis Functions ====================

def extract_constraints(text: str) -> str:
    """
    Extract constraints section from problem description.
    
    Args:
        text: Problem description text
        
    Returns:
        Extracted constraints as a string
    """
    lines = text.splitlines()
    constraints_started = False
    constraints_lines = []

    for line in lines:
        if "Constraints:" in line:
            constraints_started = True
            continue
        if constraints_started:
            # Skip empty lines at the start of constraints section
            if not constraints_lines and not line.strip():
                continue
            # Stop at the first empty line after finding constraints
            if not line.strip():
                break
            constraints_lines.append(line.strip())

    return "\n".join(constraints_lines)

def extract_function_name_with_id(signature: str, question_id: str) -> str:
    """
    Extract function name from signature and add question_id suffix
    
    Args:
        signature: Original signature string
        question_id: Question ID to append to function name
        
    Returns:
        Function name with question_id suffix, or empty string if not found
    """
    assert signature is not None
    for line in signature.split('\n'):
        if line.strip().startswith('def '):
            match = re.match(r'def\s+(\w+)', line.strip())
            if match:
                return f"{match.group(1)}_{question_id}"
    raise ValueError(f"No function name found in signature: {signature}")

def remove_class_comments(code: str) -> str:
    """
    Remove comment symbols from class definitions while keeping the actual code.
    
    Args:
        code (str): The input code string
        
    Returns:
        str: Code with class definition comments converted to actual code
    """
    lines = code.strip().split('\n')
    result_lines = []
    in_class_definition = False
    
    for line in lines:
        if line.strip().startswith('# Definition for'):
            in_class_definition = True
            continue
        if in_class_definition:
            if line.strip().startswith('class '):
                in_class_definition = False
                result_lines.append(line.strip())
            elif line.strip().startswith('# '):
                # Remove the comment symbol and keep the actual code
                result_lines.append(line.strip()[2:])
            else:
                in_class_definition = False
                result_lines.append(line)
        else:
            result_lines.append(line)
    
    return '\n'.join(result_lines)

def extract_io_types(starter_code: str) -> tuple:
    """
    Extract input and output types from a function signature in starter code.
    
    Args:
        starter_code (str): The starter code containing the function signature
        
    Returns:
        tuple: A tuple of ((param_name: param_type), (return_type1, return_type2, ...))
    """
    # Remove class definition comments
    starter_code = remove_class_comments(starter_code)
    
    # Find the function signature line
    lines = starter_code.strip().split('\n')
    print(f"All lines: {lines}")  # Debug print
    
    # Find the line containing 'def' and the function signature
    # Skip commented lines (starting with #)
    signature_line = None
    for line in lines:
        if 'def' in line and not line.strip().startswith('#'):
            signature_line = line.strip()
            break
    
    if not signature_line:
        print("No function signature found!")
        return ((), ('None',))
    
    print(f"Found signature line: {signature_line}")  # Debug print
    
    # Extract parameter types
    params_str = signature_line[signature_line.find('(')+1:signature_line.find(')')]
    print(f"Parameters string: {params_str}")  # Debug print
    param_types = []
    
    # Skip 'self' parameter if it exists
    params = [p.strip() for p in params_str.split(',') if p.strip() != 'self']
    print(f"Parameters after removing self: {params}")  # Debug print
    
    for param in params:
        if ':' in param:
            name, type_str = param.split(':', 1)  # Split only on first occurrence
            # Keep the full type annotation including Optional, List, etc.
            param_types.append(f"{name.strip()}:{type_str.strip()}")
    
    print(f"Extracted param types: {param_types}")  # Debug print
    
    # Extract return type(s)
    return_types = []
    if '->' in signature_line:
        return_type_str = signature_line.split('->')[1].strip()
        # Handle multiple return types and remove any trailing colons
        return_types = [t.strip().rstrip(':') for t in return_type_str.split(',')]
    else:
        return_types = ['None']
    
    print(f"Extracted return types: {return_types}")  # Debug print
    
    return (tuple(param_types), tuple(return_types))

def convert_io_types_to_dict(io_types: tuple) -> dict:
    """
    Convert IO types tuple to a dictionary with sets of types.
    
    Args:
        io_types (tuple): A tuple of ((param_name: param_type), (return_type1, return_type2, ...))
        
    Returns:
        dict: A dictionary with 'Input' and 'Output' types
    """
    print(f"Converting IO types: {io_types}")  # Debug print
    
    # Extract input types (preserve all types, even duplicates)
    input_types = []
    for param in io_types[0]:
        if ':' in param:
            name, type_str = param.split(':', 1)  # Split only on first occurrence
            input_types.append(type_str.strip())
    
    print(f"Extracted input types: {input_types}")  # Debug print
    
    # Extract output types (use set to remove duplicates)
    output_types = set()
    for type_str in io_types[1]:
        if type_str != 'None':  # Skip 'None' type
            output_types.add(type_str)
    
    # If no output types were found, add 'None'
    if not output_types:
        output_types.add('None')
    
    print(f"Extracted output types: {output_types}")  # Debug print
    
    return {
        "Input": tuple(input_types),  # Keep all input types
        "Output": tuple(sorted(output_types))  # Sort output types for consistency
    } 

# ==================== AST Analysis Classes ====================

class ImportAnalyzer(ast.NodeVisitor):
    """Analyzes Python code to find used imports and names"""
    
    def __init__(self):
        self.used_names: Set[str] = set()  # Names used in the code
        self.imported_names: Set[str] = set()  # Names that are imported
        self.star_imports: Set[str] = set()  # Modules with star imports
        self.defined_names: Set[str] = set()  # Names defined in the code
        self.name_contexts: Dict[str, List[Tuple[ast.AST, ast.AST]]] = {}  # Track where each name is used
        self.current_parent = None  # Track current parent node
    
    def visit(self, node: ast.AST) -> None:
        """Override visit to track parent-child relationships"""
        old_parent = self.current_parent
        self.current_parent = node
        super().visit(node)
        self.current_parent = old_parent
    
    def visit_Name(self, node: ast.Name):
        """Record used names and their context"""
        if isinstance(node.ctx, ast.Load):
            self.used_names.add(node.id)
            if node.id not in self.name_contexts:
                self.name_contexts[node.id] = []
            self.name_contexts[node.id].append((node, self.current_parent))
        elif isinstance(node.ctx, ast.Store):
            self.defined_names.add(node.id)
        self.generic_visit(node)
    
    def visit_Import(self, node: ast.Import):
        """Record imported names"""
        for name in node.names:
            if name.asname:
                self.imported_names.add(name.asname)
            else:
                self.imported_names.add(name.name)
        self.generic_visit(node)
    
    def visit_ImportFrom(self, node: ast.ImportFrom):
        """Record imported names from modules"""
        if node.module:
            if node.names[0].name == '*':
                self.star_imports.add(node.module)
            else:
                for name in node.names:
                    if name.asname:
                        self.imported_names.add(name.asname)
                    else:
                        self.imported_names.add(name.name)
        self.generic_visit(node)
    
    def visit_FunctionDef(self, node: ast.FunctionDef):
        """Record function definitions"""
        self.defined_names.add(node.name)
        self.generic_visit(node)
    
    def visit_ClassDef(self, node: ast.ClassDef):
        """Record class definitions"""
        self.defined_names.add(node.name)
        self.generic_visit(node)
    
    def visit_arg(self, node: ast.arg):
        """Record function arguments"""
        self.defined_names.add(node.arg)
        self.generic_visit(node)
    
    def visit_For(self, node: ast.For):
        """Record loop variables"""
        if isinstance(node.target, ast.Name):
            self.defined_names.add(node.target.id)
        self.generic_visit(node)
    
    def visit_comprehension(self, node: ast.comprehension):
        """Record comprehension variables"""
        if isinstance(node.target, ast.Name):
            self.defined_names.add(node.target.id)
        self.generic_visit(node)

class ImportVisitor(ast.NodeVisitor):
    """AST visitor to collect all names used in the code"""
    def __init__(self):
        self.defined_names: Set[str] = set()
        self.used_names: Set[str] = set()
        self.imported_names: Set[str] = set()
        self.current_imports: Dict[str, Set[str]] = {}
        
    def visit_Import(self, node: ast.Import) -> None:
        for name in node.names:
            self.imported_names.add(name.name)
            if name.asname:
                self.imported_names.add(name.asname)
        self.generic_visit(node)
        
    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        if node.module:
            if node.module not in self.current_imports:
                self.current_imports[node.module] = set()
            for name in node.names:
                self.imported_names.add(name.name)
                if name.asname:
                    self.imported_names.add(name.asname)
                self.current_imports[node.module].add(name.name)
        self.generic_visit(node)
        
    def visit_Name(self, node: ast.Name) -> None:
        if isinstance(node.ctx, ast.Store):
            self.defined_names.add(node.id)
        elif isinstance(node.ctx, ast.Load):
            self.used_names.add(node.id)
        self.generic_visit(node)
        
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.defined_names.add(node.name)
        self.generic_visit(node)
        
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.defined_names.add(node.name)
        self.generic_visit(node)

# ==================== Import Management Functions ====================

def analyze_imports(code: str) -> Tuple[Set[str], Set[str], Set[str]]:
    """
    Analyze code to find used imports and names.
    
    Args:
        code: Python code to analyze
        
    Returns:
        Tuple of (used_names, star_imports, defined_names)
    """
    try:
        tree = ast.parse(code)
        analyzer = ImportAnalyzer()
        analyzer.visit(tree)
        
        # Filter out names that are defined in the code
        actually_used_imports = analyzer.used_names - analyzer.defined_names
        
        # Check for name conflicts
        for name in list(actually_used_imports):
            if name in analyzer.name_contexts:
                contexts = analyzer.name_contexts[name]
                for node, parent in contexts:
                    if isinstance(parent, (ast.Call, ast.Attribute)):
                        actually_used_imports.discard(name)
                        break
        
        return actually_used_imports, analyzer.star_imports, analyzer.defined_names
    except SyntaxError:
        print("Warning: Could not parse code for import analysis")
        return set(), set(), set()

def find_missing_imports(code: str) -> Tuple[Dict[str, Set[str]], Set[str]]:
    """Find missing imports by analyzing the code using AST and dynamic module analysis."""
    # Use dynamic import mapper for better coverage
    return dynamic_mapper.find_missing_imports_dynamic(code)

def add_imports(code: str, missing_imports: Dict[str, Set[str]], current_imports: Dict[str, Set[str]]) -> str:
    """Add missing imports to the code."""
    if not missing_imports:
        return code
        
    # Generate new import statements
    new_imports = []
    for module, names in missing_imports.items():
        if module in current_imports:
            # Add only new names to existing import
            new_names = names - current_imports[module]
            if new_names:
                new_imports.append(f"from {module} import {', '.join(sorted(new_names))}")
        else:
            # Create new import statement
            new_imports.append(f"from {module} import {', '.join(sorted(names))}")
    
    if not new_imports:
        return code
        
    # Find the last import statement
    lines = code.split('\n')
    last_import_line = -1
    for i, line in enumerate(lines):
        if line.startswith(('import ', 'from ')):
            last_import_line = i
    
    # Insert new imports after the last import statement
    if last_import_line >= 0:
        lines.insert(last_import_line + 1, '\n'.join(new_imports))
    else:
        # If no imports exist, add them at the beginning
        lines.insert(0, '\n'.join(new_imports))
        lines.insert(1, '')  # Add blank line after imports
    
    return '\n'.join(lines)

def clean_imports(code: str) -> str:
    """
    Process code by:
    1. Analyzing code to find used names
    2. Adding only necessary imports using dynamic module analysis
    3. Removing unused imports
    4. Maintaining code structure and indentation
    """
    # Parse the code to find used names
    used_names, star_imports, defined_names = analyze_imports(code)
    
    # Get all imports that might be needed using dynamic analysis
    needed_imports = set()
    for name in used_names:
        # Skip names that are defined in the code
        if name in defined_names:
            continue
        
        # Use dynamic mapper to find which module contains this name
        for module_name in STD_LIB_IMPORTS.keys():
            module_attributes = dynamic_mapper.get_dynamic_imports(module_name)
            if name in module_attributes:
                needed_imports.add(f"from {module_name} import {name}")
    
    # Split code into lines
    lines = code.strip('\n').split('\n')
    
    # Find existing imports
    import_lines = []
    code_lines = []
    in_import_block = True
    for line in lines:
        if in_import_block and (line.strip().startswith('import ') or line.strip().startswith('from ')):
            import_lines.append(line)
        else:
            in_import_block = False
            code_lines.append(line)
    
    # Combine and deduplicate imports
    all_imports = sorted(set(import_lines) | needed_imports)
    
    # Build the final code
    result = []
    if all_imports:
        result.extend(all_imports)
        result.append('')  # Add blank line after imports
    result.extend(code_lines)
    
    # Remove duplicate blank lines
    final = []
    for line in result:
        if not (final and not final[-1].strip() and not line.strip()):
            final.append(line)
    
    return '\n'.join(final)

# ==================== File Processing Functions ====================

def auto_import_file(file_path: str, _) -> bool:
    """Auto-fix imports for a single file. Returns True if modified."""
    with open(file_path, 'r', encoding='utf-8') as f:
        src = f.read()
    
    missing_imports, current_imports = find_missing_imports(src)
    if not missing_imports:
        return False
        
    fixed = add_imports(src, missing_imports, current_imports)
    if fixed != src:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(fixed)
        return True
    return False

def process_file(file_path: str) -> bool:
    """
    Process a single Python file to clean its imports.
    
    Args:
        file_path: Path to the Python file
        
    Returns:
        bool: True if file was modified, False otherwise
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Skip if file already has shared imports
        if "class ListNode" in content:
            return False
        
        # Clean imports
        cleaned_content = clean_imports(content)
        
        # Write back if changed
        if cleaned_content != content:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(cleaned_content)
            return True
        
        return False
    
    except Exception as e:
        print(f"Error processing {file_path}: {str(e)}")
        return False

# ==================== Shared Imports Management Functions ====================

def get_top_level_defs(shared_code: str) -> Dict[str, ast.AST]:
    """
    Get all top-level definitions (class/def/variables) and their AST nodes.
    Returns: {name: node}
    """
    tree = ast.parse(shared_code)
    defs = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            defs[node.name] = node
        elif isinstance(node, ast.Assign):
            for t in node.targets:
                if isinstance(t, ast.Name):
                    defs[t.id] = node
    return defs

def get_used_names_in_node(node: ast.AST) -> Set[str]:
    """Get all names used in an AST node (excluding self-defined names)"""
    used = set()
    class Visitor(ast.NodeVisitor):
        def visit_Name(self, n):
            if isinstance(n.ctx, ast.Load):
                used.add(n.id)
    Visitor().visit(node)
    return used

def get_recursive_needed_defs(main_code: str, shared_code: str) -> Set[str]:
    """
    Recursively analyze all top-level definitions used in the main code (including dependency chain).
    """
    defs = get_top_level_defs(shared_code)
    main_tree = ast.parse(main_code)
    main_used = set()
    class MainVisitor(ast.NodeVisitor):
        def visit_Name(self, n):
            if isinstance(n.ctx, ast.Load):
                main_used.add(n.id)
    MainVisitor().visit(main_tree)
    needed = set()
    stack = list(main_used & set(defs.keys()))
    while stack:
        name = stack.pop()
        if name in needed:
            continue
        needed.add(name)
        node = defs[name]
        for dep in get_used_names_in_node(node):
            if dep in defs and dep not in needed:
                stack.append(dep)
    return needed

def extract_imports(shared_code: str) -> str:
    """Extract import statements from SHARED_IMPORTS (preserving order)"""
    lines = shared_code.split('\n')
    import_lines = [line for line in lines if line.strip().startswith('import ') or line.strip().startswith('from ')]
    return '\n'.join(import_lines)

def add_shared_imports_to_file(file_path: str) -> bool:
    """
    Add shared imports to a file if they don't already exist.
    
    Args:
        file_path: Path to the Python file
        
    Returns:
        bool: True if file was modified, False otherwise
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Skip if file already has shared imports
        if "class ListNode" in content:
            return False
        
        # Analyze what shared definitions are actually needed
        needed_defs = get_recursive_needed_defs(content, SHARED_IMPORTS)
        
        if not needed_defs:
            return False
        
        # Extract only the needed definitions from SHARED_IMPORTS
        defs = get_top_level_defs(SHARED_IMPORTS)
        needed_code_lines = []
        
        for line in SHARED_IMPORTS.split('\n'):
            # Check if this line defines something we need
            for def_name in needed_defs:
                if def_name in line and (line.strip().startswith('class ') or line.strip().startswith('def ') or line.strip().startswith('inf =')):
                    needed_code_lines.append(line)
                    break
            else:
                # Include lines that are part of the needed definitions
                if any(def_name in line for def_name in needed_defs):
                    needed_code_lines.append(line)
        
        needed_shared_code = '\n'.join(needed_code_lines)
        
        # Split content into imports and code
        lines = content.split('\n')
        import_lines = []
        code_lines = []
        in_import_block = True
        
        for line in lines:
            if in_import_block and (line.strip().startswith('import ') or line.strip().startswith('from ')):
                import_lines.append(line)
            else:
                in_import_block = False
                code_lines.append(line)
        
        # Build new content with shared imports
        new_content = []
        if import_lines:
            new_content.extend(import_lines)
            new_content.append('')  # Add blank line after imports
        
        # Add shared imports
        new_content.append(needed_shared_code)
        new_content.append('')  # Add blank line after shared imports
        
        # Add the rest of the code
        new_content.extend(code_lines)
        
        new_content_str = '\n'.join(new_content)
        
        # Write back if changed
        if new_content_str != content:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content_str)
            return True
        
        return False
    
    except Exception as e:
        print(f"Error processing {file_path}: {str(e)}")
        return False

def process_all_files(base_dir: str, mode: str = 'all') -> None:
    """
    Process all Python files in a directory.
    
    Args:
        base_dir: Base directory to process
        mode: Processing mode ('all', 'defs', 'imports')
    """
    base_path = Path(base_dir)
    py_files = list(base_path.rglob('*.py'))
    if not py_files:
        print(f"No Python files found in {base_dir}")
        return
    
    print(f"Found {len(py_files)} Python files to process.")
    modified_count = 0
    
    # Recursive dependency cleaning
    if mode in ('all', 'defs'):
        for file_path in tqdm(py_files, desc="Adding shared imports"):
            if add_shared_imports_to_file(str(file_path)):
                modified_count += 1
        print(f"\nShared imports addition complete. Modified {modified_count} files.")
    
    # Import static analysis cleaning
    if mode in ('all', 'imports'):
        modified_count = 0
        for file_path in tqdm(py_files, desc="Cleaning imports"):
            if process_file(str(file_path)):
                modified_count += 1
        print(f"\nImport cleaning complete. Modified {modified_count} files.")