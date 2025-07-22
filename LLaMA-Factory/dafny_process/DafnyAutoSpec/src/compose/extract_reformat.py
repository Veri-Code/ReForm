import ast
import astor
import re
from utils import *

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

class RemoveSelfTransformer(ast.NodeTransformer):
    def __init__(self):
        self.class_attrs = set()  # Store class attributes
        self.init_code = []  # Store initialization code
        self.class_name_map = {}  # Store class name mappings

    def visit_Attribute(self, node):
        # Handle attribute access, convert self.attr to attr
        if isinstance(node.value, ast.Name) and node.value.id == 'self':
            self.class_attrs.add(node.attr)
            return ast.Name(id=node.attr, ctx=node.ctx)
        return node

    def visit_FunctionDef(self, node):
        if node.args.args and node.args.args[0].arg == 'self':
            # If it's an __init__ method, collect initialization code
            if node.name == '__init__':
                for stmt in node.body:
                    if isinstance(stmt, ast.Assign):
                        for target in stmt.targets:
                            if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name) and target.value.id == 'self':
                                self.class_attrs.add(target.attr)
                                # Convert self.attr = value to attr = value
                                new_stmt = ast.Assign(
                                    targets=[ast.Name(id=target.attr, ctx=ast.Store())],
                                    value=stmt.value
                                )
                                self.init_code.append(new_stmt)
            # Remove self parameter
            node.args.args = node.args.args[1:]
            # Process attribute access in function body
            node.body = [self.visit(stmt) for stmt in node.body]
        return node

    def visit_ClassDef(self, node):
        # Keep class name unchanged
        return node

def extract_methods_from_class(code: str, task_id: str, class_name: str = "Solution") -> str:
    # First extract
    tree = ast.parse(code)
    new_body = []
    transformer = RemoveSelfTransformer()

    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            if node.name == class_name:
                # First process class definition, collect class attributes and initialization code
                for item in node.body:
                    if isinstance(item, ast.FunctionDef):
                        transformer.visit(item)
                
                # Add initialization code (skip None initialization)
                new_body.extend(transformer.init_code)
                
                # Add other methods
                for item in node.body:
                    if isinstance(item, ast.FunctionDef) and item.name != '__init__':
                        item = transformer.visit(item)
                        new_body.append(item)
            else:
                # Keep other class definitions unchanged
                new_body.append(node)
        else:
            # Keep other code unchanged
            new_body.append(node)

    new_module = ast.Module(body=new_body, type_ignores=[])
    ast.fix_missing_locations(new_module)

    try:
        extracted_code = ast.unparse(new_module)  # Python 3.9+
    except AttributeError:
        extracted_code = astor.to_source(new_module)
    
    # Then perform renaming
    return rename_after_extract(extracted_code, task_id)

def rename_after_extract(code: str, task_id: str) -> str:
    """
    Perform renaming after extraction
    
    Args:
        code: Extracted code
        task_id: Task ID
        
    Returns:
        Renamed code
    """
    tree = ast.parse(code)
    transformer = RenameTransformer(task_id)
    
    # First traversal to collect all class name mappings and global variables
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            if node.name not in transformer.class_name_map:
                transformer.class_name_map[node.name] = f"{node.name}_{task_id}"
        elif isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
            # Only collect variables in global scope
            if not any(isinstance(parent, (ast.FunctionDef, ast.ClassDef)) for parent in ast.walk(tree)):
                transformer.global_vars.add(node.targets[0].id)
        elif isinstance(node, ast.FunctionDef):
            # Only collect top-level function name mappings
            if node.name not in transformer.special_attrs and not any(isinstance(parent, (ast.FunctionDef, ast.ClassDef)) for parent in ast.walk(tree)):
                transformer.method_name_map[node.name] = f"{node.name}_{task_id}"
    
    # Then perform complete transformation
    new_tree = transformer.visit(tree)
    ast.fix_missing_locations(new_tree)
    
    # Final traversal to ensure all class name references are correctly updated
    for node in ast.walk(new_tree):
        if isinstance(node, ast.Name):
            if node.id in transformer.class_name_map:
                node.id = transformer.class_name_map[node.id]
            elif node.id in transformer.global_vars:
                node.id = f"{node.id}_{task_id}"
            elif node.id in transformer.method_name_map:
                node.id = transformer.method_name_map[node.id]
        elif isinstance(node, ast.ClassDef):
            if node.name in transformer.class_name_map:
                node.name = transformer.class_name_map[node.name]
        elif isinstance(node, ast.FunctionDef):
            # Only update top-level function names
            if node.name in transformer.method_name_map and not any(isinstance(parent, (ast.FunctionDef, ast.ClassDef)) for parent in ast.walk(tree)):
                node.name = transformer.method_name_map[node.name]
    
    try:
        return ast.unparse(new_tree)  # Python 3.9+
    except AttributeError:
        return astor.to_source(new_tree)

class RenameTransformer(ast.NodeTransformer):
    def __init__(self, task_id: str):
        self.task_id = task_id
        self.class_name_map = {}  # Store class name mappings
        self.method_name_map = {}  # Store method name mappings
        self.var_name_map = {}  # Store global variable name mappings
        self.current_scope = None  # Current scope
        self.global_vars = set()  # Store global variable names
        self.special_attrs = {'__slots__', '__init__', '__str__', '__repr__', '__eq__', '__hash__', '__lt__', '__le__', '__gt__', '__ge__'}  # Special attributes set

    def visit_ClassDef(self, node):
        # Handle class name
        if node.name not in self.class_name_map:  # Avoid duplicate processing
            class_name = f"{node.name}_{self.task_id}"
            self.class_name_map[node.name] = class_name
            node.name = class_name
        # Process class body
        old_scope = self.current_scope
        self.current_scope = "class"
        node.body = [self.visit(stmt) for stmt in node.body]
        self.current_scope = old_scope
        return node

    def visit_FunctionDef(self, node):
        # Handle method name (only top-level methods)
        if self.current_scope is None:
            if node.name not in self.method_name_map and node.name not in self.special_attrs:  # Avoid processing special methods
                method_name = f"{node.name}_{self.task_id}"
                self.method_name_map[node.name] = method_name
                node.name = method_name
        # Process function body
        old_scope = self.current_scope
        self.current_scope = "function"
        node.body = [self.visit(stmt) for stmt in node.body]
        self.current_scope = old_scope
        return node

    def visit_Name(self, node):
        # Handle class name references and method calls
        if node.id in self.class_name_map:
            return ast.Name(id=self.class_name_map[node.id], ctx=node.ctx)
        # Handle global variable references (including within functions)
        elif node.id in self.global_vars:
            return ast.Name(id=f"{node.id}_{self.task_id}", ctx=node.ctx)
        # Handle other variables in global scope
        elif self.current_scope is None:
            if node.id in self.var_name_map:
                return ast.Name(id=self.var_name_map[node.id], ctx=node.ctx)
            elif node.id in self.method_name_map:
                return ast.Name(id=self.method_name_map[node.id], ctx=node.ctx)
        # Handle function calls within functions (only top-level functions)
        elif self.current_scope == "function":
            if node.id in self.method_name_map and not any(isinstance(parent, (ast.FunctionDef, ast.ClassDef)) for parent in ast.walk(tree)):
                return ast.Name(id=self.method_name_map[node.id], ctx=node.ctx)
        return node

    def visit_Assign(self, node):
        # Handle global variable assignments
        if self.current_scope is None and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id not in self.var_name_map and node.targets[0].id not in self.special_attrs:  # Avoid processing special attributes
                var_name = f"{node.targets[0].id}_{self.task_id}"
                self.var_name_map[node.targets[0].id] = var_name
                self.global_vars.add(node.targets[0].id)  # Add to global variables set
                node.targets[0].id = var_name
        # Handle global variable assignments within functions
        elif self.current_scope == "function" and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in self.global_vars:
                node.targets[0].id = f"{node.targets[0].id}_{self.task_id}"
        return node

    def visit_Call(self, node):
        # Handle class instantiation calls and method calls
        if isinstance(node.func, ast.Name):
            if node.func.id in self.class_name_map:
                node.func.id = self.class_name_map[node.func.id]
            elif node.func.id in self.method_name_map:
                node.func.id = self.method_name_map[node.func.id]
        # Handle nested function calls
        elif isinstance(node.func, ast.Attribute):
            node.func = self.visit(node.func)
        return node

    def visit_annotation(self, node):
        # Handle class name references in type annotations
        if isinstance(node, ast.Name) and node.id in self.class_name_map:
            return ast.Name(id=self.class_name_map[node.id], ctx=node.ctx)
        elif isinstance(node, ast.Subscript):
            # Handle type annotations like List[Node]
            if isinstance(node.value, ast.Name) and node.value.id == 'List':
                node.slice = self.visit(node.slice)
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            # Handle type annotations like Node | None
            node.left = self.visit(node.left)
            node.right = self.visit(node.right)
        return node


data = jsonl_parser('../../raw_code/filtered_leetcodes.jsonl')
extracted_data = []

# Test
# transformed_code = extract_methods_from_class(example3, "123")
# print(transformed_code)
# constraints = extract_constraints(data[0]['problem_description'])
# print("Extracted Constraints:\n", constraints)
#

for item in data:
    extracted_data.append({
        "cc_complex": item["cc_complex"],
        "difficulty": item["difficulty"],
        "task_id": item["task_id"],
        "question_id": item["question_id"],
        "tags": item["tags"],
        "signature": item["starter_code"],
        "entry_point": extract_function_name_with_id(item["starter_code"], item["question_id"]),
        "constraints": extract_constraints(item["problem_description"]),
        "IO_type": extract_io_types(item["starter_code"]),
        'code': extract_methods_from_class(item["completion"], item["question_id"]),
        "IO_sample": item["input_output"],
    })
jsonl_dumper(extracted_data, '../../raw_code/reformed_leetcodes.jsonl')