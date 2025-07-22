"""
Template patterns for function composition
Each template is defined as a dictionary with:
- name: template function name
- description: docstring of the template
- pattern: list of function calls, where each call is a tuple of (input_node, output_node)
- return_nodes: list of nodes to be returned
"""

import sys
import os

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

TEMPLATE_PATTERNS = {
    'main_2node_1': {
        'name': 'main_2node_1',
        'description': '2 nodes, single chain',
        'pattern': [(None, 'o1'), ('o1', 'o2')],
        'return_nodes': ['o2']
    },
    'main_3node_2': {
        'name': 'main_3node_2',
        'description': '3 nodes, single chain',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3')],
        'return_nodes': ['o3']
    },
    'main_3node_3': {
        'name': 'main_3node_3',
        'description': '3 nodes, one splits into two',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3')],
        'return_nodes': ['o2', 'o3']
    },
    'main_4node_4': {
        'name': 'main_4node_4',
        'description': '4 nodes, single chain',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o3', 'o4')],
        'return_nodes': ['o4']
    },
    'main_4node_5': {
        'name': 'main_4node_5',
        'description': '4 nodes, chain with a branch at the second node',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o2', 'o4')],
        'return_nodes': ['o3', 'o4']
    },
    'main_4node_6': {
        'name': 'main_4node_6',
        'description': '4 nodes, root splits into two, one branch splits again',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o2', 'o4')],
        'return_nodes': ['o3', 'o4']
    },
    'main_4node_7': {
        'name': 'main_4node_7',
        'description': '4 nodes, root splits into three',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o1', 'o4')],
        'return_nodes': ['o2', 'o3', 'o4']
    },
    'main_5node_8': {
        'name': 'main_5node_8',
        'description': '5 nodes, single chain',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o3', 'o4'), ('o4', 'o5')],
        'return_nodes': ['o5']
    },
    'main_5node_9': {
        'name': 'main_5node_9',
        'description': '5 nodes, chain with a branch at the third node',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o3', 'o4'), ('o3', 'o5')],
        'return_nodes': ['o4', 'o5']
    },
    'main_5node_10': {
        'name': 'main_5node_10',
        'description': '5 nodes, chain with a branch at the second node, both branches split again',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o2', 'o4'), ('o3', 'o5')],
        'return_nodes': ['o4', 'o5']
    },
    'main_5node_11': {
        'name': 'main_5node_11',
        'description': '5 nodes, root splits into two, one branch is a chain of three',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o2', 'o4'), ('o4', 'o5')],
        'return_nodes': ['o3', 'o5']
    },
    'main_5node_12': {
        'name': 'main_5node_12',
        'description': '5 nodes, root splits into two, both branches are chains of two',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o2', 'o4'), ('o3', 'o5')],
        'return_nodes': ['o4', 'o5']
    },
    'main_5node_13': {
        'name': 'main_5node_13',
        'description': '5 nodes, root splits into two, left branch splits again',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o2', 'o4'), ('o2', 'o5')],
        'return_nodes': ['o3', 'o4', 'o5']
    },
    'main_5node_14': {
        'name': 'main_5node_14',
        'description': '5 nodes, chain then splits into three',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o2', 'o4'), ('o2', 'o5')],
        'return_nodes': ['o3', 'o4', 'o5']
    },
    'main_5node_15': {
        'name': 'main_5node_15',
        'description': '5 nodes, root splits into four',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o1', 'o4'), ('o1', 'o5')],
        'return_nodes': ['o2', 'o3', 'o4', 'o5']
    },
    'main_5node_16': {
        'name': 'main_5node_16',
        'description': '5 nodes, root splits into three, leftmost branch splits again',
        'pattern': [(None, 'o1'), ('o1', 'o2'), ('o1', 'o3'), ('o1', 'o4'), ('o2', 'o5')],
        'return_nodes': ['o3', 'o4', 'o5']
    }
}

# Explicitly define all functions
def main_2node_1(o: object) -> object:
    """2 nodes, single chain"""
    o1: object = function1(o)
    o2: object = function2(o1)
    return o2

def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    return o3

def main_3node_3(o: object) -> object:
    """3 nodes, one splits into two"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    return (o2, o3)

def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    o4: object = function4(o3)
    return o4

def main_4node_5(o: object) -> object:
    """4 nodes, chain with a branch at the second node"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    o4: object = function4(o2)
    return (o3, o4)

def main_4node_6(o: object) -> object:
    """4 nodes, root splits into two, one branch splits again"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o2)
    return (o3, o4)

def main_4node_7(o: object) -> object:
    """4 nodes, root splits into three"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o1)
    return (o2, o3, o4)

def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    o4: object = function4(o3)
    o5: object = function5(o4)
    return o5

def main_5node_9(o: object) -> object:
    """5 nodes, chain with a branch at the third node"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    o4: object = function4(o3)
    o5: object = function5(o3)
    return (o4, o5)

def main_5node_10(o: object) -> object:
    """5 nodes, chain with a branch at the second node, both branches split again"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    o4: object = function4(o2)
    o5: object = function5(o3)
    return (o4, o5)

def main_5node_11(o: object) -> object:
    """5 nodes, root splits into two, one branch is a chain of three"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o2)
    o5: object = function5(o4)
    return (o3, o5)

def main_5node_12(o: object) -> object:
    """5 nodes, root splits into two, both branches are chains of two"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o2)
    o5: object = function5(o3)
    return (o4, o5)

def main_5node_13(o: object) -> object:
    """5 nodes, root splits into two, left branch splits again"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o2)
    o5: object = function5(o2)
    return (o3, o4, o5)

def main_5node_14(o: object) -> object:
    """5 nodes, chain then splits into three"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o2)
    o4: object = function4(o2)
    o5: object = function5(o2)
    return (o3, o4, o5)

def main_5node_15(o: object) -> object:
    """5 nodes, root splits into four"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o1)
    o5: object = function5(o1)
    return (o2, o3, o4, o5)

def main_5node_16(o: object) -> object:
    """5 nodes, root splits into three, leftmost branch splits again"""
    o1: object = function1(o)
    o2: object = function2(o1)
    o3: object = function3(o1)
    o4: object = function4(o1)
    o5: object = function5(o2)
    return (o3, o4, o5)

class DAGNode:
    def __init__(self, name):
        self.name = name
        self.children = []
        self.parent = None

class DAG:
    def __init__(self, pattern):
        self.nodes = {}
        self.root = None
        self.build(pattern)

    def build(self, pattern):
        for parent, child in pattern:
            if child not in self.nodes:
                self.nodes[child] = DAGNode(child)
            if parent is not None:
                if parent not in self.nodes:
                    self.nodes[parent] = DAGNode(parent)
                self.nodes[parent].children.append(self.nodes[child])
                self.nodes[child].parent = self.nodes[parent]
            else:
                self.root = self.nodes[child]

    def get_level_groups_with_leaf_info(self):
        # Returns groups of sibling nodes at each level along with their leaf status
        if not self.root:
            return []
        result = []
        queue = [self.root]
        while queue:
            group = []
            next_queue = []
            for node in queue:
                group.append((node, len(node.children) == 0))  # (node, is_leaf)
                next_queue.extend(node.children)
            result.append(group)
            queue = next_queue
        return result

    def level_order(self):
        result = []
        if not self.root:
            return result
        queue = [self.root]
        while queue:
            node = queue.pop(0)
            result.append(node.name)
            queue.extend(node.children)
        return result

import itertools
import random

def generate_all_assignments(functions, dag, max_leaf_combos=5):
    """
    Generate all possible function assignments for the DAG structure
    Args:
        functions: List of available functions
        dag: DAG structure
        max_leaf_combos: Maximum number of combinations to generate for leaf nodes
    Returns:
        List of all possible function assignments
    """
    sibling_groups = dag.get_level_groups_with_leaf_info()
    func_indices = list(range(len(functions)))
    all_assignments = []

    def backtrack(idx, used, assignment):
        if idx == len(sibling_groups):
            all_assignments.append([list(g) for g in assignment])
            return
        group = sibling_groups[idx]
        size = len(group)
        is_leaf_group = all(is_leaf for _, is_leaf in group)
        available = [i for i in func_indices if i not in used]
        if is_leaf_group:
            combos = list(itertools.combinations(available, size))
            if len(combos) > max_leaf_combos:
                combos = random.sample(combos, max_leaf_combos)
            for combo in combos:
                assignment.append(list(combo))
                backtrack(idx + 1, used | set(combo), assignment)
                assignment.pop()
        else:
            for perm in itertools.permutations(available, size):
                assignment.append(list(perm))
                backtrack(idx + 1, used | set(perm), assignment)
                assignment.pop()
    backtrack(0, set(), [])
    return all_assignments

if __name__ == '__main__':
    pattern = TEMPLATE_PATTERNS['main_5node_15']['pattern']
    dag = DAG(pattern)
    print('Level order traversal:', dag.level_order())

    # Assume we have 5 functions
    functions = ['f1', 'f2', 'f3', 'f4', 'f5']
    assignments = generate_all_assignments(functions, dag)
    print('Number of unique assignments:', len(assignments))
    for a in assignments:
        print(a)

