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
from verl.utils.reward_score.extraction import *
from verl.utils.reward_score.condition_comparison import *
from concurrent.futures import ThreadPoolExecutor, as_completed

"""
This file is used to evaluate models using:
1. 1 for no parse error else 0
2. 1 for verifiable else 0
3. ensures ratio = # ensures / # gt_ensures
4. 1 for stronger than gt else 0
5. 1 for no cheat by assume else 0
6. 1 for no cheat by only writting ensure true else 0
7. 1 for no cheat by only writting ensure A==A else 0
8. test on DafnyBench: 1 for as strong as gt else 0
9. test on DafnyBench: ratio of matching ensures / # gt_ensures
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
    complete_ensures = extract_tosearch(input_string,'ensures'+r' (.*?)\n')
    num_ensures = len(complete_ensures)
    return num_ensures

def is_fuzzy_match(original, modified):
    """
    验证 modified 是否是 original 插入若干行以及增加或减少空白字符后得到的。
    
    :param original: 原始字符串
    :param modified: 修改后的字符串
    :return: 如果 modified 是 original 的模糊匹配结果，则返回 True，否则返回 False
    """
    # 将字符串按行分割
    original_lines = original.splitlines()
    modified_lines = modified.splitlines()
    
    # 使用 difflib.Differ 比较字符串
    differ = difflib.Differ()
    diff = list(differ.compare(original_lines, modified_lines))
    
    # 检查差异
    for (line, origin_line) in zip(diff, original_lines):
        if line.startswith('? '):  # 忽略空白字符的差异
            continue
        if line.startswith('- '):  # 原始字符串中有但修改后的字符串中没有的行
            print(origin_line)
            return False
        if line.startswith('+ '):  # 修改后的字符串中有但原始字符串中没有的行
            print(origin_line)
            continue  # 允许插入行
        if line.startswith('  '):  # 完全相同的行
            continue
    
    return True

def tidy_dafny_code(dafny_code: str) -> str:
    """
     re-formats the extracted Dafny to consistent indentation and brace placement 
     so that any minor formatting won't trip the verifier
    """
    # Step 1: Normalize braces
    dafny_code = re.sub(r'\s*{\s*', ' {\n', dafny_code)  # Add newline after '{'
    dafny_code = re.sub(r'\s*}\s*', '\n}\n', dafny_code)  # Add newline before '}'

    # Step 2: Normalize indentation and special case handling
    lines = dafny_code.splitlines()
    indented_lines = []
    indent_level = 0

    for line in lines:
        stripped_line = line.strip()

        # Skip empty lines
        if not stripped_line:
            continue
        
        # Handle keywords and function/method signatures
        if re.match(r'^\s*(function|method|ghost|ensures|requires|invariant|while|if|else|return|assume)\s', stripped_line):
            if re.match(r'^\s*(function|method|ghost|assume)\s', stripped_line):
                indented_lines.append(' ' * indent_level + stripped_line)
                indent_level += 4
            else:
                indented_lines.append(' ' * indent_level + stripped_line)
        
        # Handle closing braces
        elif stripped_line == '}':
            indent_level -= 4
            indented_lines.append(' ' * indent_level + stripped_line)
        
        # General statements
        else:
            indented_lines.append(' ' * indent_level + stripped_line)

    # Step 3: Handle special cases for keywords
    tidy_code = '\n'.join(indented_lines)
    tidy_code = re.sub(r'(\b(?:ensures|requires|invariant|ensuresforall|ensuresexists|assume)\b)', r'\n\1', tidy_code)

    # Step 4: Remove unnecessary blank lines and finalize indentation
    tidy_code = re.sub(r'\n\s*\n', '\n\n', tidy_code)

    # Correct indentation for blocks
    lines = tidy_code.split('\n')
    indent_level = 0
    formatted_lines = []

    for line in lines:
        line = line.strip()
        if line.endswith('{'):
            formatted_lines.append('    ' * indent_level + line)
            indent_level += 1
        elif line.endswith('}'):
            indent_level -= 1
            formatted_lines.append('    ' * indent_level + line)
        elif line == '':
            formatted_lines.append('')
        else:
            formatted_lines.append('    ' * indent_level + line)
    
    return '\n'.join(formatted_lines)


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
        
    dir = os.path.join(output_dir, exp_name, str(index))
    os.makedirs(dir, exist_ok=True)
    os.chdir(dir)

    try:
        num_files = len(os.listdir(dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = f"{number}.dfy"
        outfn = f"out-{number}.txt"
        errfn = f"err-{number}.txt"

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
    except:
        pass
    # finally:
    #     os.chdir(old_dir)
    # remove new dir generated.
    # os.system("rm -rf " + dir)

    return {"status": status, "log": log, "out": outlog}

def execute_diff_location(cmd, ext, v, timeout_sec=10, index=-1, exp_name="exp", output_dir=None):
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
        
    dir = os.path.join(output_dir, exp_name, "dafny", str(index))
    os.makedirs(dir, exist_ok=True)
    os.chdir(dir)

    try:
        num_files = len(os.listdir(dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = f"{number}.dfy"
        outfn = f"out-{number}.txt"
        errfn = f"err-{number}.txt"

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
    except:
        pass

    return {"status": status, "log": log, "out": outlog}

def compute_subset_score(solution_str, 
                        ground_truth, 
                        exp_name, 
                        index, 
                        method='strict',
                        num_examine=0, 
                        compile_score=0.2,
                        score=0.4, 
                        think_score=0.0,
                        ensures_score=0.4,
                        fail_execute_score=0.01,
                        parse_score=0.0,
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
    1. 1 for stronger than gt else 0
    2. requires_coverage
    3. ensures_coverage
    4. 1 for verifiable else 0
    """

    scores = (0,) * 4

    if output_dir is None:
        raise ValueError("output_dir must be provided")
    
    _dir = os.path.join(output_dir, exp_name, str(index))
    os.makedirs(_dir, exist_ok=True)
    os.chdir(_dir)
        
    gt_code = ground_truth['ground_truth']   
    code = extract_solution(solution_str=solution_str)
    input_code = extract_input(solution_str=solution_str)

    if input_code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = f"{number}.dfy"
        f = open(fn, "w")
        f.write("No input found")
        f.close()
        # print(f"Solution string: {solution_str}")
        print("No input found")
        return scores
    
    do_print = False

    if code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = f"{number}.dfy"
        f = open(fn, "w")
        f.write("No codestring found")
        f.close()
        if do_print:
            print(f"No codestring found")
        return scores

    num_gt_ensures = find_num_ensures(gt_code)
    num_ensures = find_num_ensures(code)
    ratio = num_ensures / num_gt_ensures


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
        fn = f"{number}.dfy"
        f = open(fn, "w")
        f.write("original code changed")
        f.close()
        # print(code)
        # print(input_code)
        print("original code changed")
        return scores
    
    # print(code)
    
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30, index=index, exp_name=exp_name, output_dir=output_dir)
    
    def check_parse_errors(out_dict):
        if 'parse errors detected' in out_dict["out"]:
            if do_print:
                print("Execution result: Parse Errors Detected.")
            return True


        if 'resolution/type error' in out_dict["out"]:
            if do_print:
                print("Execution result: Resolution/Type Error.")
            return True
        
        return False
    
    # Create output filename based on input file
    num_files = len(os.listdir(os.path.join(_dir, "dafnyBench")))
    number = num_files * 10000 + random.randint(0, 9999)
    fn = f"{number}.json"
    output_file = os.path.join(_dir, "dafnyBench", fn)
    
    # Analyze coverage
    requires_coverage, ensures_coverage = analyze_spec_coverage(gt_code, code, output_file)
    scores[1], scores[2] = requires_coverage, ensures_coverage
    
    if ' 0 errors' in return_dict["out"]:
        scores[3] = 1
        try: 
            if version == "one_score":
                new_dafny = strip_specs_and_inject_asserts(gt_code, code, key="one_score")
                one_score_dict = execute_diff_location("dafny verify", "dfy", new_dafny, timeout_sec=30, index=index, exp_name=exp_name, output_dir=output_dir)
                if check_parse_errors(one_score_dict):
                    return (compile_score + think_score +score + parse_score, 0,1,1)
                errors = one_score_dict["out"].count("assertion might not hold")
                strong = errors==0
                scores[0] = strong
        except Exception as e:
            print(f"{bcolors.WARNING}An error occurred! {bcolors.ENDC}")
            print("An error occurred:", e)
            # print(code)
            print("#"*30)
        return scores
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return scores

