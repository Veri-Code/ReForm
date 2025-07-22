import re
import os
import copy
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed, ProcessPoolExecutor
import logging
import random
from typing import List, Union, Dict, Optional

import tempfile
import subprocess
from tqdm import tqdm
import functools

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

### 1. Formatting Utils.
def depend_remove(original_code: str) -> str:
    '''
    Remove all dependencies related - start with 'include'.
    '''
    if not original_code:
        return ''
    
    lines = original_code.split('\n')
    filtered_lines = []
    
    for line in lines:
        line_stripped = line.strip()
        if line_stripped.startswith('include '):
            continue
        filtered_lines.append(line)
    
    result = '\n'.join(filtered_lines)
    
    result = re.sub(r'\n{2,}', '\n', result.strip())
    
    return result

def emptyline_remove(code: str) -> str:
    '''
    Remove all empty lines of given codes.
    '''
    if not code:
        return ''
    
    code = '\n'.join([l for l in code.split('\n') if l.strip() != ''])
    return code

def comment_remove(code):
    """
    Remove C++ style comments from code:
    - Single-line comments: //
    - Multi-line comments: /* */
    """
    if not code:
        return ""

    result = []
    i = 0
    in_string = False
    string_char = None
    in_single_comment = False
    comment_nesting_level = 0
    
    while i < len(code):
        # Handle strings (to avoid detecting comments in strings)
        if not in_single_comment and comment_nesting_level == 0:
            if code[i] in ['"', "'"]:
                if not in_string:
                    in_string = True
                    string_char = code[i]
                    result.append(code[i])
                elif code[i] == string_char and code[i-1] != '\\':
                    in_string = False
                    result.append(code[i])
                else:
                    result.append(code[i])
                i += 1
                continue
        
        if in_string:
            result.append(code[i])
            i += 1
            continue
        
        # Handle single-line comment
        if i < len(code) - 1 and code[i:i+2] == '//' and comment_nesting_level == 0:
            in_single_comment = True
            i += 2
            continue
        
        # End of single-line comment
        if in_single_comment and code[i] == '\n':
            in_single_comment = False
            result.append('\n')  # Preserve the newline
            i += 1
            continue
        
        # Skip characters in single-line comment
        if in_single_comment:
            i += 1
            continue
        
        # Handle multi-line comment start
        if i < len(code) - 1 and code[i:i+2] == '/*':
            comment_nesting_level += 1
            i += 2
            continue
        
        # Handle multi-line comment end
        if i < len(code) - 1 and code[i:i+2] == '*/' and comment_nesting_level > 0:
            comment_nesting_level -= 1
            i += 2
            continue
        
        # Skip characters in multi-line comment
        if comment_nesting_level > 0:
            i += 1
            continue
        
        # Normal code - append to result
        result.append(code[i])
        i += 1
    
    return ''.join(result)

def hacking_remove(dafny_code: str) -> str:
    """
    Remove all lines from a Dafny code string that match the following patterns:
    1. Lines starting with 'ensures true', 'ensures false', 'invariant true', 'invariant false', 'assume true', or 'assume false'.
    2. Lines matching the pattern '<keyword> <var> <logic_op> <var>', where <keyword> is any of the keywords in key_words (e.g., 'ensures', 'requires', 'assert', 'assume'),
       <logic_op> is any of the logic_ops (e.g., '==', '!='), and <var> is the same variable name on both sides.

    Args:
        dafny_code: A string containing Dafny code
    Returns:
        A cleaned Dafny code string with specified lines removed (Only consider single-specifications under this scope)
    """
    lines: list[str] = dafny_code.split('\n')
    filtered_lines: list[str] = []
    # Pattern for logical equal or inequal
    key_words = ["ensures", "requires", "assert", "assume"]
    logic_ops = ["==", "!="]
    equal_patterns: list[re.Pattern] = [
        re.compile(rf'^\s*{kw}\s+(\w+)\s*{re.escape(logic)}\s*\1\s*$', re.IGNORECASE)
        for kw in key_words
        for logic in logic_ops
    ]
    for line in lines:
        stripped = line.strip()
        if (
            stripped.startswith('ensures true') or
            stripped.startswith('ensures false') or
            stripped.startswith('invariant true') or
            stripped.startswith('invariant false') or
            stripped.startswith('assume false') or
            stripped.startswith('assume true') or
            any(pattern.match(line) for pattern in equal_patterns)
        ):
            continue
        filtered_lines.append(line)
    return '\n'.join(filtered_lines)

def hint_remove_old(
    original_code: str,
    remove_keywords: List[str] = ['requires', 'ensures', 'invariant', 'assert', 'modifies', 'assume', 'reads', 'decreases'],
    declarations: List[str] = ["method", "function", "lemma"]) -> str:
    """
    General function to remove lines in the code that start with specific keywords.
    
    Parameters:
    - original_code: The original code as a string.
    - remove_keywords: A list of keywords indicating which lines to remove. 
      Default is ['requires', 'ensures', 'invariant', 'assert', 'modifies', 'assume', 'reads', 'decreases'].
    - declarations: A list of declarations to remove lines within. 
      Default is ["method", "function", "lemma"].
                    
    Returns:
    - The modified code as a string.
    """
    lines = original_code.split('\n')
    keep_lines = []
    
    # If no declarations are provided, remove all matching lines (similar to hint_remove)
    if declarations is None:
        for line in lines:
            if any(line.strip().startswith(kw) for kw in remove_keywords):
                continue
            keep_lines.append(line)
        return '\n'.join(keep_lines)
    
    # If declarations are provided, remove specified lines only within declaration blocks (similar to hint_remove_v2)
    else:
        concat_dec = '|'.join(declarations)
        regex = r'^\s*({})\b'.format(concat_dec)
        declaration_pattern = re.compile(regex)
        in_declaration = False

        for line in lines:
            if in_declaration:
                # Check if the start of a block is encountered: contains '{'
                if '{' in line:
                    in_declaration = False
                    keep_lines.append(line)
                else:
                    # Skip the line if it starts with a specified keyword, otherwise keep it
                    if any(line.lstrip().startswith(kw) for kw in remove_keywords):
                        continue
                    else:
                        keep_lines.append(line)
            else:
                # If a declaration line is detected, enable in_declaration mode
                if declaration_pattern.match(line):
                    in_declaration = True
                    keep_lines.append(line)
                else:
                    keep_lines.append(line)

        return '\n'.join(keep_lines)

def remove_complex_specs(
    code: str,
    remove_keywords: list[str]
) -> str:
    """
    Remove multi-line, block, and 'by' specifications.
    Also handles complex specifications with logical operators and parentheses.
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
        # complex spec with parentheses: starts with keyword and has (
        elif spec_pattern.match(line) and '(' in line:
            # Track parentheses balance
            paren_balance = line.count('(') - line.count(')')
            i += 1
            # Continue until we find matching closing parenthesis
            while i < n and paren_balance > 0:
                paren_balance += lines[i].count('(') - lines[i].count(')')
                i += 1
            continue
        # multi-line continuation: starts with keyword, next line is deeper indented
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

def hint_remove_pure(
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

def suffix_remove(code):
    """Remove markdown code block suffix if present"""
    return code.rstrip('`') if code.endswith('```') else code

def extract_dafny_code(text: str) -> str:
    """Extract code between ```dafny and ```"""
    match = re.search(r"```dafny\s*(.*?)\s*```", text, re.DOTALL)
    return suffix_remove(match.group(1)) if match else None

def extract_btw_special_token_pair(text: str, token: str) -> list[str]:
    # Use regex or string methods, but do NOT decode or encode escapes!
    pattern = re.compile(rf"<{token}>(.*?)</{token}>", re.DOTALL)
    return [m.group(1) for m in pattern.finditer(text)]

### 2.Dafny Verifications
def dafny_verify(
        command_def: list[str],
        dafny_dict: dict, 
        code_field: str='dafny', 
        log_file: str=None):
    '''
    Verify a single sample with Dafny with log files or log to console.
    Through the process, add the field ['v_state'] to label the verification result.
    Also, add the Dafny verifier output to the field ['compiler'].
    '''

    if log_file:
        logging.basicConfig(
            filename=log_file,
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            filemode='a'  # appending style
        )
    else:
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s'
        )

    with tempfile.NamedTemporaryFile(suffix='.dfy', delete=False) as temp_file:
        temp_file.write(dafny_dict[code_field].encode('utf-8'))
        temp_file.flush()
        dafny_file = temp_file.name
        logging.info("Temporary .dfy contents:\n%s", open(dafny_file, 'r').read())
        logging.info(f"Created temporary file: {dafny_file}")
    try:
        cmd = command_def + [dafny_file]
        logging.info(f"Running command: {' '.join(cmd)}")
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=True
        )
        # Save verifier output to 'compiler' field
        dafny_dict['compiler'] = (result.stdout or '') + (result.stderr or '')
        logging.info(f"Stdout: {result.stdout}")
        if "parse errors detected" in result.stdout:
            print(f"{bcolors.WARNING}Parse Errors!{bcolors.ENDC}")
        if " 0 errors" in result.stdout:
            dafny_dict['v_state'] = 1
            if 'uuid' in dafny_dict:
                logging.info(f"{dafny_dict['uuid']} Passed.")
            else:
                logging.info(f"Passed.")
        else:
            dafny_dict['v_state'] = 0
            if 'uuid' in dafny_dict:
                logging.info(f"{dafny_dict['uuid']} Failed.")
            else:
                logging.info(f"Failed.")
    except subprocess.CalledProcessError as e:
        logging.error(f"Stdout: {e.stdout}")
        # Save verifier output to 'compiler' field even on error
        dafny_dict['compiler'] = (e.stdout or '') + (e.stderr or '')
        dafny_dict['v_state'] = 0
        if " 0 errors" in e.stdout:
            dafny_dict['v_state'] = 1
            if 'uuid' in dafny_dict:
                logging.info(f"{dafny_dict['uuid']} Passed.")
            else:
                logging.info(f"Passed.")
        elif 'uuid' in dafny_dict:
            logging.info(f"{dafny_dict['uuid']} Failed with error returncode={e.returncode}.")
        else:
            logging.info(f"Failed with error returncode={e.returncode}.")
    except FileNotFoundError:
        # Almost impossible to happen due to the temporary file mechanism.
        logging.error("dafny not found in PATH")
    finally:
        # Delete the temporary file.
        if os.path.exists(dafny_file):
            os.remove(dafny_file)
            logging.info(f"Deleted temporary file: {dafny_file}\n\n \n\n")

def parallel_version(
        command_def: list[str],
        dafny_codes: list[dict], 
        code_field: str='dafny',
        log_file: str=None,
        max_workers: int = 4,
    ):
    '''
    Parallel verification in hope of reducing the time cost.
    '''

    max_workers = min(max_workers, os.cpu_count())

    bound_func = functools.partial(dafny_verify, 
                                   command_def, 
                                   code_field=code_field, 
                                   log_file=log_file)
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(bound_func, dafny_code) for dafny_code in dafny_codes]
        for future in tqdm(as_completed(futures), 
                           total=len(dafny_codes), 
                           desc="Verifying", 
                           unit="task"):
            try:
                # Due to the stuck case in Dafny-train.
                future.result()
            except Exception as e:
                logging.error(f"Error in parallel execution: {e}")