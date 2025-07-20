import re
import random
import ast
import operator
import difflib
import math
import os
import hashlib
import sys
# sys.path.append(os.path.dirname(os.path.abspath(__file__)))
# sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from verl.utils.reward_score.naive_reward import *
# from verl.utils.reward_score.extraction import *
from verl.utils.reward_score.condition_comparison_fixed import strip_specs_and_inject_asserts, strip_specs_and_inject_equivalence
from verl.utils.reward_score.naive_reward import *
from concurrent.futures import ThreadPoolExecutor, as_completed
from verl.inference.reward_score.spec_coverage import *

"""
This file is used to evaluate models using:
1. 1 for no parse error else 0 (OR)
2. 1 for verifiable else 0 (OR)
3. 1 for containing all gt ensures (OR)

4. 1 for no cheat by adding assume else 0 (avg)
5. 1 for no cheat by only writting ensure true only for a method else 0 (avg)
6. 1 for no cheat by only writting ensure A==A only for a method else 0 (avg)

7. num of intermediate clauses (avg)
8. 1 for passing gt spec (OR)
9. 1 for stronger than gt else 0 (OR)
"""


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

def count_words(input_string):
    return len(input_string.split())

def find_num_ensures(input_string):
    complete_ensures = extract_tosearch(input_string,'ensures')
    num_ensures = len(complete_ensures)
    return num_ensures


def execute(cmd, ext, v, timeout_sec=10, index=-1, exp_name="exp", output_dir=None):
    """Execute a command with the given parameters.
    
    Args:
        cmd: Command to execute
        ext: File extension
        v: Content to write to file
        timeout_sec: Timeout in seconds
        index: Index for directory naming
        exp_name: Experiment name
        output_dir: Directory to store output files
    """
    if output_dir is None:
        raise ValueError("output_dir must be provided")
        
    dir = os.path.join(output_dir, str(index))
    os.makedirs(dir, exist_ok=True)
    # os.chdir(dir)

    num_files = len(os.listdir(dir))
    number = num_files * 10000 + random.randint(0, 9999)
    fn = os.path.join(dir, f"{number}.dfy")
    outfn = os.path.join(dir, f"out-{number}.txt")
    errfn = os.path.join(dir, f"err-{number}.txt")

    f = open(fn, "w")
    f.write(v)
    f.close()


    runcmd = "timeout --kill-after=5 %s %s %s >%s 2>%s" % (str(timeout_sec), cmd, fn, outfn, errfn)
    # if use_sandbox:
    #     if docker_sandbox:
    #         runcmd = 'docker run --rm --platform linux/amd64 -v "$(pwd):/app" namin/llm-verified ' + runcmd.replace(fn, "/app/"+fn)
    #     else:
    #         pre_llm_command = "singularity exec --no-mount=/n --no-mount=/net --no-mount=/scratch --no-mount=/cvmfs ~/singularity/llm-verified_latest.sif"
    #         runcmd = "SINGULARITY_HOME=/ timeout 10 %s %s %s >%s 2>%s" % (pre_llm_command, cmd, fn, outfn, errfn)

    #print("RUN CMD:", runcmd)
    status = os.system(runcmd)

    f = open(outfn, "r")
    outlog = f.read()
    f.close()

    f = open(errfn, "r", encoding='utf-8')
    log = f.read()
    f.close()

    sys_error_prefix = "sh: line 1:"
    if log.startswith(sys_error_prefix):
        raise RuntimeError(
            log[len(sys_error_prefix) :]
            + " -- install tool locally or set livecode to True for lightweight testing"
        )
    
    return {"status": status, "log": log, "out": outlog}

def execute_diff_location(cmd, ext, v, timeout_sec=10, index=-1, exp_name="exp", output_dir=None, name=None):
    """Execute a command in a different location.
    
    Args:
        cmd: Command to execute
        ext: File extension
        v: Content to write to file
        timeout_sec: Timeout in seconds
        index: Index for directory naming
        exp_name: Experiment name
        output_dir: Directory to store output files
    """
    if output_dir is None:
        raise ValueError("output_dir must be provided")
    
    if name is None:
        dir = os.path.join(output_dir, str(index), "specRefine")
    else:
        dir = os.path.join(output_dir, str(index), name)
    os.makedirs(dir, exist_ok=True)
    # os.chdir(dir)

    num_files = len(os.listdir(dir))
    number = num_files * 10000 + random.randint(0, 9999)
    fn = os.path.join(dir, f"{number}.dfy")
    outfn = os.path.join(dir, f"out-{number}.txt")
    errfn = os.path.join(dir, f"err-{number}.txt")

    f = open(fn, "w")
    f.write(v)
    f.close()


    runcmd = "timeout --kill-after=5 %s %s %s >%s 2>%s" % (str(timeout_sec), cmd, fn, outfn, errfn)
    
    status = os.system(runcmd)
    
    f = open(outfn, "r")
    outlog = f.read()
    f.close()

    f = open(errfn, "r", encoding='utf-8')
    log = f.read()
    f.close()

    sys_error_prefix = "sh: line 1:"
    if log.startswith(sys_error_prefix):
        raise RuntimeError(
            log[len(sys_error_prefix) :]
            + " -- install tool locally or set livecode to True for lightweight testing"
        )

    return {"status": status, "log": log, "out": outlog}

def extract_tosearch(code, tosearch):
    """ Extracts assume statements from Dafny code """
    # This regular expression matches assume statements assuming they end with a semicolon
    assume_pattern = re.compile(tosearch)
    assumes = assume_pattern.findall(code)
    return set(assumes)

def no_ensures_true_at_all(complete_code):
    # return True, None
    complete_ensures = extract_tosearch(complete_code,r'ensures\s+(true)')
    # print("DEBUG: ", complete_ensures)
    if len(complete_ensures) != 0:
        # print("DEBUG- no_ensures_true_at_all: ", complete_ensures)
        return False
    return True

def no_only_ensures_true_for_any_method(complete_code):
    specs = extract_specs(complete_code)
    # print("DEBUG: ", specs)
    for key, value in specs.items():
        if value["ensures"] == ["true"]:
            return False
    return True

def no_ensures_equiv_at_all(complete_code):
    # return True, None
    complete_ensures = extract_tosearch(complete_code,r'ensures\s+(\w+)\s*==\s*\1\s*')
    if len(complete_ensures) != 0:
        # print("DEBUG- no_ensures_equiv_at_all: ", complete_ensures)
        return False
    return True

def no_only_ensures_equiv_for_any_method(complete_code):
    equiv_pattern = re.compile(r'\s*(\w+)\s*==\s*\1\s*')
    specs = extract_specs(complete_code)
    for key, value in specs.items():
        if len(value['ensures'])==1 and equiv_pattern.search(value["ensures"][0]):
            return False
    return True


def no_assume_at_all(complete_code):
    # Extract assume statements from both pieces of code
    complete_assumes = extract_tosearch(complete_code,'assume'+r' (.*?);')
    if len(complete_assumes) != 0:
        # print("DEBUG- no_assume_at_all: ", complete_assumes)
        return False
    return True

def no_added_assume(original, modified):
    """
    Check if there are any newly added lines that start with 'assume'
    
    Args:
        original: Original code string
        modified: Modified code string
        
    Returns:
        bool: True if no new assume statements were added, False otherwise
    """
    # Split into lines
    original_lines = original.splitlines()
    original_lines = [line.strip() for line in original_lines]
    modified_lines = modified.splitlines()
    modified_lines = [line.strip() for line in modified_lines]
    
    # Use difflib to get differences
    differ = difflib.Differ()
    diff = list(differ.compare(original_lines, modified_lines))
    
    # Check only the added lines (lines starting with '+ ')
    for line in diff:
        if line.startswith('+ '):  # This is an added line
            # Remove the '+ ' prefix and check if it starts with 'assume'
            actual_line = line[2:].strip()
            if actual_line.startswith('assume'):
                return False
                
    return True

def count_intermediate(complete_code):
    clause_list = ['invariant','assert']
    pattern = re.compile(r'|'.join(clause_list))
    clauses = pattern.findall(complete_code)
    return len(clauses)

def reinsert_gt_spec(gt_code, llm_code):
    """Insert gt spec into llm code by replacing method/function signatures.
    
    Args:
        gt_code: Ground truth code containing the specs to insert
        llm_code: LLM generated code to modify
        
    Returns:
        Modified llm_code with gt specs inserted, or error message string
    """
    
    def find_method_signature_end(code, start_pos):
        """Find the end of a method signature by looking for the method body opening brace.
        
        Searches for lines that start with '{' (possibly with whitespace) and returns
        the position after the opening brace when all parentheses (), [], and <> are balanced.
        If we encounter a semicolon, we return the position after it.
        """
        # Extract the code section from start_pos to end of code
        section = code[start_pos:]
        # brace_pattern = re.compile(r'\{\s*\n|\{.*;\s*\n')
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
                    return start_pos + current_pos + brace_pos + 1  # Return position after the opening brace
            
            # Update balances for this line
            paren_balance += line.count('(') - line.count(')')
            square_balance += line.count('[') - line.count(']')
            angle_balance += line.count('<') - line.count('>')
            braces_balance += line.count('{') - line.count('}')

            if any(line.strip().startswith(kw) for kw in ['method', 'function', 'constructor', 'lemma', 'class', 'predicate', 'two_state', 'ghost']):
                return start_pos + current_pos

            # Check for semicolon when brackets are balanced
            if line.strip().endswith(';'):
                return -1
            # Move to next line (add 1 for the newline character)
            current_pos += len(line) + 1
        
        return -1  # Not found
    
    # Find method/function signatures in gt_code using a simpler initial pattern
    sig_re = re.compile(
        r'((?:ghost\s+)?(?:method|function)\s+(?:\{:axiom\}\s+)?(\w+))', 
        re.DOTALL | re.MULTILINE
    )
    gt_parts = []
    
    for match in sig_re.finditer(gt_code):
        name = match.group(2)
        start_pos = match.start()
        end_pos = find_method_signature_end(gt_code, match.end())
        
        if end_pos != -1:
            full_signature = gt_code[start_pos:end_pos]
            gt_parts.append({
                'name': name,
                'start': start_pos,
                'end': end_pos,
                'signature': full_signature
            })
    
    # Collect all replacements to perform them in reverse order
    replacements = []
    
    for gt_part in gt_parts:
        name = gt_part['name']
        escaped = re.escape(name)
        
        # Find corresponding method in LLM code
        method_start_re = re.compile(
            rf'((?:ghost\s+)?(?:method|function)\s+{escaped})',
            re.DOTALL | re.MULTILINE
        )
        llm_match = method_start_re.search(llm_code)
        
        if llm_match:
            llm_end_pos = find_method_signature_end(llm_code, llm_match.end())
            if llm_end_pos != -1:
                replacements.append({
                    'start': llm_match.start(),
                    'end': llm_end_pos,
                    'replacement': gt_part['signature'],
                    'name': name
                })
            else:
                # print("DEBUG- llm_code: ", llm_code)
                # print("DEBUG- name: ", name)
                # print(f"Warning: Could not find method body opening brace for '{name}' in LLM code")
                pass
        else:
            # print(f"Warning: Could not find method/function '{name}' in LLM code")
            pass
    
    # Sort replacements by start position in reverse order to avoid index shifting
    replacements.sort(key=lambda x: x['start'], reverse=True)
    
    # Apply replacements
    for repl in replacements:
        # print(f"DEBUG- repl['replacement']: {repl['replacement']}")
        # print(f"DEBUG- llm_code[repl['start']]: {llm_code[repl['start']:repl['end']]}")
        llm_code = llm_code[:repl['start']] + repl['replacement'] + llm_code[repl['end']:]
    
    # Handle constructors separately with the same approach
    constructor_re = re.compile(
        r'((?:ghost\s+)?(?:constructor))',
        re.DOTALL | re.MULTILINE
    )
    
    gt_constructors = []
    for match in constructor_re.finditer(gt_code):
        start_pos = match.start()
        end_pos = find_method_signature_end(gt_code, match.end())
        if end_pos != -1:
            gt_constructors.append({
                'start': start_pos,
                'end': end_pos,
                'signature': gt_code[start_pos:end_pos]
            })
    
    llm_constructors = []
    for match in constructor_re.finditer(llm_code):
        start_pos = match.start()
        end_pos = find_method_signature_end(llm_code, match.end())
        if end_pos != -1:
            llm_constructors.append({
                'start': start_pos,
                'end': end_pos,
                'signature': llm_code[start_pos:end_pos]
            })
    
    if len(gt_constructors) != len(llm_constructors):
        # print(f"Warning: Number of constructors in gt ({len(gt_constructors)}) and llm ({len(llm_constructors)}) are not the same")
        return llm_code
    
    # Collect constructor replacements in reverse order
    constructor_replacements = []
    for gt_const, llm_const in zip(gt_constructors, llm_constructors):
        constructor_replacements.append({
            'start': llm_const['start'],
            'end': llm_const['end'],
            'replacement': gt_const['signature']
        })
    
    # Sort by start position in reverse order
    constructor_replacements.sort(key=lambda x: x['start'], reverse=True)
    
    # Apply constructor replacements
    for repl in constructor_replacements:
        # print(f"DEBUG- repl['replacement']: {repl['replacement']}")
        # print(f"DEBUG- llm_code[repl['start']]: {llm_code[repl['start']:repl['end']]}")
        llm_code = llm_code[:repl['start']] + repl['replacement'] + llm_code[repl['end']:]
    return llm_code

def no_comments(code):
    pattern = re.compile(r'//.*')
    return not pattern.search(code)

def compute_subset_score(solution_str, 
                        ground_truth, 
                        exp_name, 
                        index, 
                        method='strict',
                        num_examine=0, 
                        version="one_score",
                        output_dir=None,
                        eval_plot=False,
                        inference=False):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        exp_name: experiment name
        index: index for directory naming
        method: the method to extract the solution
        num_examine: number of examples to examine
        version: version of scoring to use
        output_dir: directory to store output files
        
    Returns:
        tuple: (stronger than gt or not, verifiable, no parse error, ensures ratio)
    """
    """
    This file is used to evaluate models using:
    1. 1 for no parse error else 0
    2. 1 for verifiable else 0
    3. 1 for subset score (OR)
    
    4. 1 for no cheat by adding assume else 0 (avg)
    5. 1 for no cheat by only writting ensure true only for a method else 0 (avg)
    6. 1 for no cheat by only writting ensure A==A only for a method else 0 (avg)
    
    7. num of intermediate clauses (avg)
    8. 1 for no comments(ALL)
    9. 1 for novel spec (OR)
    """
    do_print = False
    
    if output_dir is None:
        raise ValueError("output_dir must be provided")
        
    if eval_plot:
        gt_code = ground_truth
        code = solution_str
        if "No code string found" in code or "No input found" in code or "original code changed" in code:
            return [0,]*9
        input_code = code
    else:
        gt_code = ground_truth['ground_truth']   
        code = extract_solution(solution_str=solution_str)
        input_code = extract_input(solution_str=solution_str)

    _dir = os.path.join(output_dir, str(index))
    os.makedirs(_dir, exist_ok=True)

    if not os.path.exists(os.path.join(_dir, "gt.dfy")):
        fn = os.path.join(_dir, "gt.dfy")
        f = open(fn, "w")
        f.write(gt_code)
        f.close()

    scores = [0,] * 9

    if code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No codestring found")
        f.close()
        if do_print:
            print(f"No codestring found")
        return scores

    # Check various conditions
    scores[3] = int(no_added_assume(gt_code, code))
    scores[4] = int(no_only_ensures_true_for_any_method(code))
    scores[5] = int(no_only_ensures_equiv_for_any_method(code))
    scores[7] = int(no_comments(code))

    if input_code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No input found")
        f.close()
        # print(f"Solution string: {solution_str}")
        print("No input found")
        return scores

    num_gt_ensures = find_num_ensures(gt_code)
    num_ensures = find_num_ensures(code)
    ratio = num_ensures / num_gt_ensures if num_gt_ensures > 0 else 0


    if do_print:
        print(f"--------------------------------")
        print(f"num_gt_ensures: {num_gt_ensures}")
        print(f"num_ensures: {num_ensures}")
        print(f"Complete code: {gt_code}")
        print(f"Extracted code: {code}")
        print(f"Solution string: {solution_str}")

    if not is_fuzzy_match(input_code, code):
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("original code changed")
        f.close()

        # print("DEBUG: original code changed")
        # print("code: ", code)
        # print("input_code: ", input_code)
        # print("gt_code: ", gt_code)
        # print("index: ", index)
        # print("original code changed")
        # fn = f"{number}.json"
        # output_file = os.path.join(_dir, fn)
        
        # # Analyze coverage
        # requires_coverage, ensures_coverage = analyze_spec_coverage(gt_code, code, output_file)
        # print("requires_coverage: ", requires_coverage)
        # print("ensures_coverage: ", ensures_coverage)
        return scores

    # if inference:
    #     num_files = len(os.listdir(_dir))
    #     number = num_files * 10000 + random.randint(0, 9999)
    #     fn = os.path.join(_dir, f"{number}.dfy")

    #     f = open(fn, "w")
    #     f.write(code)
    #     f.close()

    #     return scores

    # print(code)
    # #ensures / #gt_ensures
    # Create output filename based on input file
    os.makedirs(os.path.join(_dir, "coverage"), exist_ok=True)
    num_files = len(os.listdir(os.path.join(_dir, "coverage")))
    number = num_files * 10000 + random.randint(0, 9999)
    fn = os.path.join(_dir, "coverage", f"{number}.json")
    output_file = os.path.join(_dir, "coverage", fn)
    
    # # Analyze coverage
    # requires_coverage, ensures_coverage = analyze_spec_coverage(gt_code, code, output_file)
    # # scores[10], scores[11] = requires_coverage, ensures_coverage
    # scores[2] = 1.0 if ensures_coverage == 1.0 else 0.0

    scores[6] = count_intermediate(code) 
    # gt_insert_code = reinsert_gt_spec(gt_code, code) 
    # intermediate_dict = execute_diff_location("dafny verify", "dfy", gt_insert_code, timeout_sec=30, index=index, exp_name=exp_name, output_dir=output_dir, name="intermediate")
    # if 'parse errors detected' in intermediate_dict["out"] or 'resolution/type error' in intermediate_dict["out"]:
    #     scores[8] = 0
    # elif ' 0 errors' in intermediate_dict["out"]:
    #     scores[8] = 1
    # else:
    #     scores[8] = 0

    try:
        merge_code_dir = "/nas/shared/sys2/liyizhi/folder-0630/sft_all_merge_128"
        merge_code = os.path.join(merge_code_dir, f"{index}.dfy")
        with open(merge_code, "r") as f:
            merge_code = f.read()
        output_file = os.path.join(_dir, "equiv")
        try:
            new_dafny = strip_specs_and_inject_equivalence(merge_code, code ,output_file=output_file)
            one_score_dict = execute_diff_location("dafny verify", "dfy", new_dafny, timeout_sec=30, index=index, exp_name=exp_name, output_dir=output_dir, name="equiv")
        except Exception as e:
            print(f"An error occurred: {e}")
            one_score_dict={}
            one_score_dict["out"]="parse errors detected"
        if 'parse errors detected' in one_score_dict["out"] or 'resolution/type error' in one_score_dict["out"]:
            scores[8] = 0
        else:
            errors = one_score_dict["out"].count("assertion might not hold")
            func_errors = one_score_dict["out"].count("a postcondition could not be proved on this return path")
            strong = errors!=0 or func_errors!=0
            if new_dafny.count("assert")>0 or new_dafny.count("ensures")>0:
                scores[8] = int(strong )
            else:
                scores[8] = 0
    except:
        scores[8] = 0

    # Verify code merge_code -> code
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30, index=index, exp_name=exp_name, output_dir=output_dir)
    # print(return_dict)
    if 'parse errors detected' in return_dict["out"]:
        scores[0] = 0
    elif 'resolution/type error' in return_dict["out"]:
        scores[0] = 0
    # successfully compiled
    else:
        # No parse error
        scores[0] = 1

    # Verifiable check
    if ' 0 errors' in return_dict["out"]:
        scores[1] = 1
        output_file = os.path.join(_dir, "extract")
        try:
            new_dafny = strip_specs_and_inject_asserts(gt_code, code, key="one_score",output_file=output_file)
            assert_count = new_dafny.count("assert")
            one_score_dict = execute_diff_location("dafny verify", "dfy", new_dafny, timeout_sec=30, index=index, exp_name=exp_name, output_dir=output_dir)
        except Exception as e:
            print(f"An error occurred: {e}")
            one_score_dict={}
            one_score_dict["out"]="parse errors detected"
        if 'parse errors detected' in one_score_dict["out"] or 'resolution/type error' in one_score_dict["out"]:
            scores[2] = 0
        else:
            errors = one_score_dict["out"].count("assertion might not hold")
            func_errors = one_score_dict["out"].count("a postcondition could not be proved on this return path")
            strong = errors==0
            func_strong = func_errors==0
            if new_dafny.count("assert")>0 or new_dafny.count("ensures")>0:
                scores[2] = int(strong * func_strong)
            else:
                scores[2] = 0
            # scores[8] = int(no_comments(code))
        # except Exception as e:
        #     print(f"{bcolors.WARNING}An error occurred! {bcolors.ENDC}")
        #     print("An error occurred:", e)
        #     # print(code)
        #     print("#"*30)
        #     scores[8] = 0
        #     # scores[8] = int(no_comments(code))
        return scores
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        # scores[8] = int(no_comments(code))
        return scores


def compute_score_with_log(llm_code, 
                        gt_code, 
                        index, 
                        exp_name,
                        method='strict',
                        num_examine=0, 
                        version="one_score",
                        output_dir=None):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        exp_name: experiment name
        index: index for directory naming
        method: the method to extract the solution
        num_examine: number of examples to examine
        version: version of scoring to use
        output_dir: directory to store output files
        
    Returns:
        tuple: (stronger than gt or not, verifiable, no parse error, ensures ratio)
    """
    """
    This file is used to evaluate models using:
    1. 1 for no parse error else 0
    2. 1 for verifiable else 0
    3. 1 for containing all gt ensures (OR)
    
    4. 1 for no cheat by adding assume else 0 (avg)
    5. 1 for no cheat by only writting ensure true only for a method else 0 (avg)
    6. 1 for no cheat by only writting ensure A==A only for a method else 0 (avg)
    
    7. num of intermediate clauses (avg)
    8. 1 for passing gt spec (OR)
    9. No Comments (OR)
    """
    return [0] * 9

# Alternative approach using more structured parsing (commented out for reference)
"""
def reinsert_gt_spec_structured(gt_code, llm_code):
    '''
    Alternative approach that could be more robust:
    1. Parse both codes to extract method signatures and their positions
    2. Create a mapping of method names to their specs
    3. Build the new code by replacing specs while preserving method bodies
    
    This approach would be more resilient to formatting differences and edge cases.
    '''
    
    def extract_method_info(code):
        '''Extract method information including name, signature, and body positions'''
        methods = {}
        
        # More comprehensive regex that captures the full method structure
        method_pattern = re.compile(
            r'((?:ghost\s+)?(?:method|function)\s+(\w+)[^{]*\{)',
            re.DOTALL | re.MULTILINE
        )
        
        for match in method_pattern.finditer(code):
            name = match.group(2)
            if name:
                methods[name] = {
                    'signature_start': match.start(),
                    'signature_end': match.end(),
                    'full_signature': match.group(1)
                }
        
        return methods
    
    gt_methods = extract_method_info(gt_code)
    llm_methods = extract_method_info(llm_code)
    
    # Build replacement list
    replacements = []
    for name, gt_info in gt_methods.items():
        if name in llm_methods:
            llm_info = llm_methods[name]
            replacements.append({
                'start': llm_info['signature_start'],
                'end': llm_info['signature_end'],
                'replacement': gt_info['full_signature'],
                'name': name
            })
    
    # Apply replacements in reverse order
    replacements.sort(key=lambda x: x['start'], reverse=True)
    
    result_code = llm_code
    for repl in replacements:
        result_code = result_code[:repl['start']] + repl['replacement'] + result_code[repl['end']:]
    
    return result_code
"""

