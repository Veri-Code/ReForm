import re
import random
import ast
import operator
import difflib
import math
import os
import hashlib
import json

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def remove_complex_specs(
        code: str,
        remove_keywords: list[str]
    ) -> str:
    """
    Remove multi-line, block, and 'by' specifications.
    """
    lines = code.split('\n')
    keep_lines = []
    i = 0
    n = len(lines)
    spec_pattern = re.compile(r'^\s*(' + '|'.join(re.escape(k) for k in remove_keywords) + r')\b')
    while i < n:
        line = lines[i]
        # block spec: starts with keyword and has { or by
        if spec_pattern.match(line) and ('{' in line or re.search(r'\bby\b', line)):
            # skip entire block
            brace_balance = line.count('{') - line.count('}')
            i += 1
            while i < n and brace_balance > 0:
                brace_balance += lines[i].count('{') - lines[i].count('}')
                i += 1
            continue
        # multi-line continuation: starts with keyword, next line is deeper indented
        elif spec_pattern.match(line) and '(' in line:
            # skip entire block
            brace_balance = line.count('(') - line.count(')')
            i += 1
            while i < n and brace_balance > 0:
                brace_balance += lines[i].count('(') - lines[i].count(')')
                i += 1
            continue
        elif spec_pattern.match(line) and '[' in line:
            # skip entire block
            brace_balance = line.count('[') - line.count(']')
            i += 1
            while i < n and brace_balance > 0:
                brace_balance += lines[i].count('[') - lines[i].count(']')
                i += 1
            continue
        elif spec_pattern.match(line):
            indent = len(line) - len(line.lstrip(' '))
            i += 1
            while i < n and (len(lines[i]) - len(lines[i].lstrip(' '))) > indent:
                i += 1
            continue
        else:
            keep_lines.append(line)
            i += 1
    return '\n'.join(keep_lines)

def remove_singleline_specs(
    code: str,
    remove_keywords: list[str]
) -> str:
    """
    Remove all single-line specifications.
    """
    pattern = re.compile(r'^\s*(' + '|'.join(re.escape(k) for k in remove_keywords) + r')\b.*$', re.MULTILINE)
    return pattern.sub('', code)

def emptyline_remove(code: str) -> str:
    '''
    Remove all empty lines of given codes.
    '''
    if not code:
        return ''
    
    code = '\n'.join([l for l in code.split('\n') if l.strip() != ''])
    return code

def hint_remove(
        original_code: str,
        remove_keywords: list[str] = ['requires', 'ensures', 'invariant', 'assert', 'modifies', 'assume', 'reads', 'decreases'],
    ) -> str:
    """
    Remove all Dafny specifications (multi-line, block, by, and single-line).
    """
    code = remove_complex_specs(original_code, remove_keywords)
    code = remove_singleline_specs(code, remove_keywords)
    code = emptyline_remove(code)
    return code
def extract_clauses(block: str, keyword: str) -> list[str]:
    """
    From a block of Dafny code, return every clause that begins
    with `keyword` (e.g. 'requires' or 'ensures'), capturing all
    lines up to (but not including) the next STOP_KEYWORD line.
    """
    lines = block.splitlines()
    clauses = []
    i = 0
    stop_kw = ["requires", "ensures", "decreases", "reads", "modifies"]

    while i < len(lines):
        line = lines[i].lstrip()
        if line.strip().startswith("{"):
            break
        if line.startswith(keyword):
            # Start collecting this clause
            collected = [ line[len(keyword):].strip() ]  # drop the leading keyword
            i += 1
            # Gather lines until the next STOP_KEYWORD or end of block
            while i < len(lines):
                nxt = lines[i].lstrip()
                # if next line begins with any stop keyword, break
                if any(nxt.startswith(kw) for kw in stop_kw) or nxt.strip().endswith(";"):
                    break
                # otherwise, include this line
                collected.append(nxt)
                i += 1
            # join and normalize whitespace
            clause_text = " ".join(p for p in collected if p).strip()
            if clause_text.endswith("{"):
                clause_text = clause_text[:-1]  # Remove the last character
            clauses.append(clause_text)
        else:
            i += 1
    return clauses or []


def extract_specs(dafny_code: str):
    """
    Returns a dict:
      { method_name: {"requires": [ ... ], "ensures": [ ... ]} }
    """
    
    def find_method_signature_end(code, start_pos):
        """Find the end of a method signature by looking for the method body opening brace.
        
        The method body opening brace should be at the beginning of a line (possibly with whitespace),
        distinguishing it from braces within specifications like ensures result.Keys >= {"dummy"}.
        If we encounter a semicolon, we return the position after the last brace we saw.
        """
        pos = start_pos
        last_brace_pos = -1
        next_method_pattern = re.compile(r'^\s*(?:method|function|constructor|lemma|class|predicate|two_state|ghost)\s+\w+')
        match = next_method_pattern.match(code[pos:])
        if match:
            end_pos = pos + match.start()
        else:
            end_pos = len(code)
        
        while pos < end_pos:
            if code[pos] == '{':
                # Record this brace position
                last_brace_pos = pos
                
                # Check if this brace is at the start of a line (method body opening)
                # Look backwards to see if there's only whitespace before this brace on the line
                line_start = code.rfind('\n', 0, pos) + 1
                before_brace = code[line_start:pos].strip()
                
                if before_brace == '':  # Only whitespace before the brace on this line
                    return pos + 1  # Return position after the opening brace
                    
            # elif code[pos] == ';':
            #     # Found semicolon, return position after the last brace we saw
            #     if last_brace_pos != -1:
            #         return last_brace_pos + 1
            #     else:
            #         # No brace found before semicolon, this might be a method declaration
            #         return pos + 1
                    
            pos += 1
            
        return -1  # Not found
    
    specs = {}
    
    # Find method/function signatures using a simpler initial pattern
    sig_re = re.compile(
        r'((?:ghost\s+)?(?:method|function)\s+(\w+))',
        re.DOTALL | re.MULTILINE
    )
    
    parts = []
    for match in sig_re.finditer(dafny_code):
        name = match.group(2)
        start_pos = match.start()
        end_pos = find_method_signature_end(dafny_code, match.end())
        
        if end_pos != -1:
            parts.append({
                'match': match,
                'name': name,
                'start': start_pos,
                'end': end_pos
            })
    
    for part in parts:
        name = part['name']
        start = part['start']
        end = part['end']
        # Extract the block from start to just before the opening brace
        block = dafny_code[start:end-1]

        # Match requires/ensures up to the next keyword (no semicolons needed)
        reqs = extract_clauses(block, 'requires')
        enss = extract_clauses(block, 'ensures')

        specs[name] = {"requires": reqs, "ensures": enss}

    return specs


def conj(exprs):
    """Parenthesize and &&-join a list of expressions."""
    exprs = ["(" +  exp+")"  for exp in exprs]
    return "(" + " && ".join( exprs ) + ")"

import re

def count_members(dafny_code: str):
    """Count the number of functions and methods"""
    # Pattern matches:
    #   optional "ghost ", then "method" or "function", then whitespace + name
    sig_re = re.compile(r'((?:ghost\s+)?(?:method|function)\s+(\w+)[^{]*{)', re.MULTILINE)
    all_sigs = sig_re.findall(dafny_code)

    counts = {
        "non-ghost":      0,
        "ghost": 0,
    }
    count = 0
    for full_sig, name in all_sigs:
        count +=1
        sig = full_sig.strip()
        if sig.startswith("ghost method") or sig.startswith("ghost function"):
            counts["ghost"] += 1
        elif sig.startswith("method") or sig.startswith("function"):
            counts["non-ghost"] += 1

    return counts, count

def parse_method(m, code):
    """Return the start and end tokens' positions of a method"""
    hdr_start = m.start()

    # Use the same robust logic as find_method_signature_end to find the method body opening brace
    def find_method_body_start(code, start_pos):
        """Find the method body opening brace, handling braces in specifications.
        
        Searches for lines that start with '{' (possibly with whitespace) and returns
        the position when all parentheses (), [], and <> are balanced.
        """
        # Extract the code section we're analyzing
        section = code[start_pos:]
        lines = section.split('\n')
        
        # Track balance of different bracket types
        paren_balance = 0  # ()
        square_balance = 0  # []
        angle_balance = 0   # <>
        braces_balance = 0
        
        current_pos = 0
        for i, line in enumerate(lines):
            # Check if this line starts with a brace and all brackets are balanced
            if line.strip().startswith('{'):
                if paren_balance == 0 and square_balance == 0 and angle_balance == 0 and braces_balance == 0:
                    # Find the actual position of the brace in the original code
                    brace_pos = line.find('{')
                    return start_pos + current_pos + brace_pos, False

            # Update balances for this line
            paren_balance += line.count('(') - line.count(')')
            square_balance += line.count('[') - line.count(']')
            angle_balance += line.count('<') - line.count('>')
            braces_balance += line.count('{') - line.count('}')

            if any(line.strip().startswith(kw) for kw in ['method', 'function', 'constructor', 'lemma', 'class', 'predicate', 'two_state', 'ghost']):
                return start_pos + current_pos, True
            # Move to next line (add 1 for the newline character)
            current_pos += len(line) + 1
            
            # # If we encounter a semicolon on a line by itself or with only whitespace,
            # # this might be a method declaration without implementation
            # if line.strip().endswith(';') and paren_balance == 0 and square_balance == 0 and angle_balance == 0:
            #     return -1, None  # No method body
        
        return -1, None  # Not found

    # Find the method body opening brace
    method_body_start, no_braces = find_method_body_start(code, m.end())

    if method_body_start == -1:
        # This might be a method declaration without implementation
        # Check if there's a semicolon

        # print(f"{bcolors.WARNING}No method body found for method parsing!{bcolors.ENDC}")
        return None, None, None

    if no_braces:
        return hdr_start, method_body_start, no_braces
    # Now perform brace matching to find the complete method body
    brace_idx = method_body_start
    depth, i = 1, brace_idx + 1
    while i < len(code) and depth > 0:
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
        i += 1
    
    if depth != 0:
        print(f"{bcolors.WARNING}Unmatched braces for method parsing! Depth: {depth}{bcolors.ENDC}")
        return None, None, None

    # Return the complete method from start to end (including closing brace)
    return hdr_start, i, no_braces
        

def split_top_level(s: str, sep: str = ',') -> list[str]:
    """
    Split string s on sep at top-level, ignoring separators inside (), <>, [], {}.
    """
    parts = []
    buf = []
    depth = {'(': 0, ')': 0, '<': 0, '>': 0, '[': 0, ']': 0, '{': 0, '}': 0}
    matching = {')': '(', '>': '<', ']': '[', '}': '{'}
    for ch in s:
        if ch in '(<[{':
            depth[ch] += 1
        elif ch in ')}]>':
            depth[matching[ch]] -= 1
        if ch == sep and all(v == 0 for v in depth.values()):
            parts.append(''.join(buf).strip())
            buf = []
        else:
            buf.append(ch)
    if buf:
        parts.append(''.join(buf).strip())
    return parts


def rewrite_returns(signature: str, body: str, assertion: str) -> str:
    """
    Rewrite each 'return ...;' in body by assigning to declared return variables,
    handling nested commas correctly, then insert assertion at end of each return.
    """
    # Extract declared return-variable names robustly
    ret_clause = re.search(r'returns\s*\(\s*([^)]*)\)', signature)
    if not ret_clause:
        print(f"{bcolors.WARNING}No return clause found for method: {signature}{bcolors.ENDC}")
        return body
    ret_vars_str = ret_clause.group(1)
    var_parts = split_top_level(ret_vars_str)
    var_names = [p.split(':', 1)[0].strip() for p in var_parts]

    # Pattern for top-level return statements
    return_re = re.compile(r'^(?P<indent>\s*)return\s+(?P<expr>.+?);', flags=re.MULTILINE)

    def repl(m):
        expr_str = m.group('expr')
        exprs = split_top_level(expr_str)
        if len(exprs) != len(var_names):
            raise ValueError(f"Arity mismatch: {len(exprs)} exprs vs {len(var_names)} vars")
        indent = m.group('indent')
        lines = []
        for name, expr in zip(var_names, exprs):
            lines.append(f"{indent}{name} := {expr};")
        lines.append(f"{indent}{assertion}")
        return '\n'.join(lines)

    return return_re.sub(repl, body)


def strip_specs_and_inject_asserts(gt_code: str, ex_code: str, key: str="one_score",output_file: str="") -> str:
    """ 
    Generate a new dafny file to compare 
    requirements and post-condtions between gt and llm codes.
    
    key: 
    requires - compare if requirements of llm code are weaker than gt;
    ensures - compare under the intersection of requirements between gt and llm, if post-conditions of llm code are stronger;
    one-score - the requirements should be weaker and under the requirements of gt, post-condtions should be stronger.
    
    """
    
    # Extract method specifications of each method.
    # gt for ground_truth and ex for llm generated code.
    gt_specs = extract_specs(gt_code)
    ex_specs = extract_specs(ex_code)
    
    # Clean up all specs in the llm code.
    stripped = hint_remove(ex_code)
    
    def inject_before_implicit_return(method_text: str, signature: str, meth: str, no_braces: bool) -> str:
        """
        Insert assertion before every line in a function body that:
        - Does NOT end with a semicolon,
        - Is not blank or just a brace,
        - Does not start with any SPECIAL_KEYWORDS.
        """

        # Keywords that should *not* receive injection in front of them
        SPECIAL_KEYWORDS = {
            'requires', 'ensures', 'invariant', 'assert',
            'modifies', 'assume', 'reads', 'decreases', 'reveal',
            'while', 'if', 'else', 'match', 'then', 'function',
            'ghost','two_state','method','class', 'predicate', "case", "default",
        }

        return_pattern = re.compile(r'((?:ghost\s+)?function\s+(\w+).*?\:\s*\((\w+)\:.*?\)\s*\n)', re.MULTILINE)
        return_var = return_pattern.search(method_text)
        if return_var:
            gt = gt_specs.get(meth, {"requires":[], "ensures":[]})
            ex = ex_specs.get(meth, {"requires":[], "ensures":[]})
            gt_conj = conj(gt["requires"])
            ex_conj = conj(ex["requires"])
            if key == "requires":
                assertion = f"ensures {gt_conj} ==> {ex_conj} \n"
            elif key == "ensures":
                if gt["ensures"] == []:
                    assertion = "ensures true \n"
                elif ex["ensures"] == []:
                    assertion = "ensures false \n"
                else:
                    gt_conj_ensures = conj(gt["ensures"])
                    ex_conj_ensures = conj(ex["ensures"])
                    assertion = f"ensures {gt_conj_ensures} <== {ex_conj_ensures} \n"
            elif key == "one_score":
                if gt["ensures"] == []:
                    assertion = "ensures true \n"
                elif ex["ensures"] == []:
                    assertion = "ensures false \n"
                else:
                    gt_conj_ensures = conj(gt["ensures"])
                    ex_conj_ensures = conj(ex["ensures"])
                    # assertion = f"assert {gt_conj} ==> {ex_conj};\n assert {gt_conj_ensures} <== {ex_conj_ensures};\n"
                    assertion = f"ensures {gt_conj} ==> {ex_conj} \n ensures {gt_conj} ==> ({gt_conj_ensures} <== {ex_conj_ensures}) \n"
                    if ex["requires"] == []:
                        assertion = f"ensures {gt_conj_ensures} <== {ex_conj_ensures} \n"
                    if gt["requires"] == [] and ex["requires"] != []:
                        assertion = "ensures false\n"
            else:
                print(f"{bcolors.WARNING}Condition comparision key cannot be recognized!{bcolors.ENDC}")

            
            if ex["ensures"] == ["true"]:
                assertion = "ensures false \n"

            # if meth not in gt_specs:
            #     assertion = "ensures false \n"
            
            equiv_pattern = re.compile(r'\s*(\w+)\s*==\s*\1\s*')
            if len(ex['ensures'])==1 and equiv_pattern.search(ex["ensures"][0]) and len(gt["ensures"]) > 1:
                assertion = "ensures false \n"
            sig_end = return_var.end()
            return method_text[:sig_end] +  assertion + method_text[sig_end:]
        else:
            return method_text

    def inject(method_text, signature, meth, no_braces):
        # 3) build your assertion string
        gt = gt_specs.get(meth, {"requires":[], "ensures":[]})
        ex = ex_specs.get(meth, {"requires":[], "ensures":[]})
        gt_conj = conj(gt["requires"])
        ex_conj = conj(ex["requires"])
        if key == "requires":
            assertion = f"assert {gt_conj} ==> {ex_conj};\n"
        elif key == "ensures":
            if gt["ensures"] == []:
                assertion = "assert true;\n"
            elif ex["ensures"] == []:
                assertion = "assert false;\n"
            else:
                gt_conj_ensures = conj(gt["ensures"])
                ex_conj_ensures = conj(ex["ensures"])
                assertion = f"assert {gt_conj_ensures} <== {ex_conj_ensures};\n"
        elif key == "one_score":
            if gt["ensures"] == []:
                assertion = "assert true; \n"
            elif ex["ensures"] == []:
                assertion = "assert false; \n"
            else:
                gt_conj_ensures = conj(gt["ensures"])
                ex_conj_ensures = conj(ex["ensures"])
                assertion = f"assert {gt_conj} ==> {ex_conj}; \n assert {gt_conj} ==> ({gt_conj_ensures} <== {ex_conj_ensures}); \n"
                if ex["requires"] == []:
                    assertion = f"assert {gt_conj_ensures} <== {ex_conj_ensures};\n"
                if gt["requires"] == [] and ex["requires"] != []:
                    assertion = "assert false;\n"
        else:
            print(f"{bcolors.WARNING}Condition comparision key cannot be recognized!{bcolors.ENDC}")
        
        if ex["ensures"] == ["true"]:
            assertion = "assert false;\n"

        equiv_pattern = re.compile(r'\s*(\w+)\s*==\s*\1\s*')
        if len(ex['ensures'])==1 and equiv_pattern.search(ex["ensures"][0]):
            assertion = "assert false;\n"
        
        # if meth not in gt_specs:
        #     assertion = "assert false; \n"


        # return_pattern = re.compile(r'((?:ghost\s+)?method\s+(\w+).*?\n)', re.MULTILINE)
        # return_var = return_pattern.search(method_text)
        # sig_end = return_var.end()
        # return method_text[:sig_end] +  assertion + method_text[sig_end:]
        # 4) if there is at least one return, rewrite all of them...
        if "return " in method_text:
            # Extract the full method signature line from method_text 
            lines = method_text.split('\n')
            full_signature = ""
            for line in lines:
                full_signature += line.strip() + " "
                if line.strip().startswith('{'):
                    # Remove the opening brace and everything after it
                    full_signature = full_signature.split('{')[0].strip()
                    break
            new_body = rewrite_returns(full_signature, method_text, assertion)
        elif no_braces:
            new_body = method_text + "\n{" + assertion + "}\n"
        else:
            new_body = method_text[:-1] + "\n" + assertion + "}\n"

        # 5) reassemble and return
        return new_body

    # run your existing pattern.sub with this inject
    pattern = re.compile(r'((?:ghost\s+)?(?:method|function)\s+(?:\{:axiom\}\s+)?(\w+))', re.MULTILINE)
    
    matches = []
    for m in pattern.finditer(stripped):
        start, end, no_braces = parse_method(m, stripped)
        if start == None:
            continue
        sig, name = m.group(1), m.group(2)  # Now group(2) is correctly the function name
        # print("parsed method: ", stripped[start:end])
        matches.append((start, end, no_braces, sig, name))
    
    extract_info = {}
    # Now do replacements from last to first:
    result = stripped
    for start, end, no_braces, sig, name in reversed(matches):
        full = result[start:end]
        if 'function' in sig:
            # treat as function
            new_block = inject_before_implicit_return(full, sig, name, no_braces)
            # continue
        else:
            # treat as method/constructor
            gt = gt_specs.get(name, {"requires":[], "ensures":[]})
            ex = ex_specs.get(name, {"requires":[], "ensures":[]})
            extract_info[name] = {"gt": gt, "ex": ex}
            extract_info[name]['block']=full
            extract_info[name]['no_braces'] = no_braces
            new_block = inject(full, sig, name, no_braces)
            extract_info[name]['new_block'] = new_block
        result = result[:start] + new_block + result[end:]
    if not os.path.exists(output_file):
        os.makedirs(output_file, exist_ok=True)
    output_file =os.path.join(output_file, "extract_info.json")
    with open(output_file, 'w') as f:
        json.dump(extract_info, f, indent=2)

    return result

def strip_specs_and_inject_equivalence(gt_code: str, ex_code: str, output_file: str="") -> str:
    """ 
    Generate a new dafny file to compare 
    requirements and post-condtions between gt and llm codes.
    
    key: 
    requires - compare if requirements of llm code are weaker than gt;
    ensures - compare under the intersection of requirements between gt and llm, if post-conditions of llm code are stronger;
    one-score - the requirements should be weaker and under the requirements of gt, post-condtions should be stronger.
    
    """
    
    # Extract method specifications of each method.
    # gt for ground_truth and ex for llm generated code.
    gt_specs = extract_specs(gt_code)
    ex_specs = extract_specs(ex_code)
    
    # Clean up all specs in the llm code.
    stripped = hint_remove(ex_code)
    
    def inject_before_implicit_return(method_text: str, signature: str, meth: str, no_braces: bool) -> str:
        """
        Insert assertion before every line in a function body that:
        - Does NOT end with a semicolon,
        - Is not blank or just a brace,
        - Does not start with any SPECIAL_KEYWORDS.
        """

        # Keywords that should *not* receive injection in front of them
        SPECIAL_KEYWORDS = {
            'requires', 'ensures', 'invariant', 'assert',
            'modifies', 'assume', 'reads', 'decreases', 'reveal',
            'while', 'if', 'else', 'match', 'then', 'function',
            'ghost','two_state','method','class', 'predicate', "case", "default",
        }

        return_pattern = re.compile(r'((?:ghost\s+)?function\s+(\w+).*?\:\s*\((\w+)\:.*?\)\s*\n)', re.MULTILINE)
        return_var = return_pattern.search(method_text)
        if return_var:
            gt = gt_specs.get(meth, {"requires":[], "ensures":[]})
            ex = ex_specs.get(meth, {"requires":[], "ensures":[]})
            gt_conj = conj(gt["requires"])
            ex_conj = conj(ex["requires"])
            if gt["ensures"] == []:
                gt["ensures"] = ["true"]
            gt_conj_ensures = conj(gt["ensures"]+ex['requires'])
            ex_conj_ensures = conj(gt["ensures"]+ex["ensures"]+ex['requires'])
            assertion = f"ensures {gt_conj_ensures} == {ex_conj_ensures} \n"
            sig_end = return_var.end()
            return method_text[:sig_end] +  assertion + method_text[sig_end:]
        else:
            return method_text

    def inject(method_text, signature, meth, no_braces):
        # 3) build your assertion string
        gt = gt_specs.get(meth, {"requires":[], "ensures":[]})
        ex = ex_specs.get(meth, {"requires":[], "ensures":[]})
        gt_conj = conj(gt["requires"])
        ex_conj = conj(ex["requires"])
        if gt["ensures"] == []:
            gt["ensures"] = ["true"]
        gt_conj_ensures = conj(gt["ensures"]+ex['requires'])
        ex_conj_ensures = conj(gt["ensures"]+ex["ensures"]+ex['requires'])
        assertion = f"assert {gt_conj_ensures} == {ex_conj_ensures};\n"

        # return_pattern = re.compile(r'((?:ghost\s+)?method\s+(\w+).*?\n)', re.MULTILINE)
        # return_var = return_pattern.search(method_text)
        # sig_end = return_var.end()
        # return method_text[:sig_end] +  assertion + method_text[sig_end:]
        # 4) if there is at least one return, rewrite all of them...
        if "return " in method_text:
            # Extract the full method signature line from method_text 
            lines = method_text.split('\n')
            full_signature = ""
            for line in lines:
                full_signature += line.strip() + " "
                if line.strip().startswith('{'):
                    # Remove the opening brace and everything after it
                    full_signature = full_signature.split('{')[0].strip()
                    break
            new_body = rewrite_returns(full_signature, method_text, assertion)
        elif no_braces:
            new_body = method_text + "\n{" + assertion + "}\n"
        else:
            new_body = method_text[:-1] + "\n" + assertion + "}\n"

        # 5) reassemble and return
        return new_body

    # run your existing pattern.sub with this inject
    pattern = re.compile(r'((?:ghost\s+)?(?:method|function)\s+(?:\{:axiom\}\s+)?(\w+))', re.MULTILINE)
    
    matches = []
    for m in pattern.finditer(stripped):
        start, end, no_braces = parse_method(m, stripped)
        if start == None:
            continue
        sig, name = m.group(1), m.group(2)  # Now group(2) is correctly the function name
        # print("parsed method: ", stripped[start:end])
        matches.append((start, end, no_braces, sig, name))
    
    extract_info = {}
    # Now do replacements from last to first:
    result = stripped
    for start, end, no_braces, sig, name in reversed(matches):
        full = result[start:end]
        if 'function' in sig:
            # treat as function
            new_block = inject_before_implicit_return(full, sig, name, no_braces)
            # continue
        else:
            # treat as method/constructor
            gt = gt_specs.get(name, {"requires":[], "ensures":[]})
            ex = ex_specs.get(name, {"requires":[], "ensures":[]})
            extract_info[name] = {"gt": gt, "ex": ex}
            extract_info[name]['block']=full
            extract_info[name]['no_braces'] = no_braces
            new_block = inject(full, sig, name, no_braces)
            extract_info[name]['new_block'] = new_block
        result = result[:start] + new_block + result[end:]
    if not os.path.exists(output_file):
        os.makedirs(output_file, exist_ok=True)
    output_file =os.path.join(output_file, "extract_info.json")
    with open(output_file, 'w') as f:
        json.dump(extract_info, f, indent=2)

    return result
