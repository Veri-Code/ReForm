import re
import random
import ast
import operator

def extract_think_process(solution_str):
    if "Assistant:" in solution_str:
        solution_str = solution_str.split("Assistant:", 1)[1]
    elif "<|im_start|>assistant" in solution_str:
        solution_str = solution_str.split("<|im_start|>assistant", 1)[1]
    else:
        return None
    think_pattern = r'<think>(.*?)```dafny'
    match = re.finditer(think_pattern, solution_str, re.DOTALL)
    matches = list(match)
    if matches:
        final_answer = matches[-1].group(1).strip()
        final_answer = final_answer.replace('```dafny', '').strip()
    else:
        final_answer = None
    return final_answer
    
def extract_solution(solution_str):
    """Extract the equation from the solution string."""
    # Remove everything before the first "Assistant:"
    if "Assistant:" in solution_str:
        solution_str = solution_str.split("Assistant:", 1)[1]
    elif "<|im_start|>assistant" in solution_str:
        solution_str = solution_str.split("<|im_start|>assistant", 1)[1]
    else:
        return None
    # solution_str = solution_str.split('\n')[-1]

    answer_pattern = r'<answer>(.*?)</answer>'
    match = re.finditer(answer_pattern, solution_str, re.DOTALL)
    matches = list(match)
    if matches:
        final_answer = matches[-1].group(1).strip()

        final_answer = final_answer.replace('```dafny', '').strip()
        final_answer = final_answer.replace('```', '').strip()
        final_answer = final_answer.replace('<|im_start|>', '').strip()
        # final_ansewr = final_answer.replace('<|im_end|>', '').strip()
    else:
        answer_pattern = r'<answer>(.*?)<\|im_end\|>'
        match = re.finditer(answer_pattern, solution_str, re.DOTALL)
        matches = list(match)
        if matches:
            final_answer = matches[-1].group(1).strip()
            final_answer = final_answer.replace('```dafny', '').strip()
            final_answer = final_answer.replace('```', '').strip()
            final_answer = final_answer.replace('<|im_start|>', '').strip()
            # final_ansewr = final_answer.replace('<|im_end|>', '').strip()
        else:
            answer_pattern = r'```dafny(.*?)```'
            match = re.finditer(answer_pattern, solution_str, re.DOTALL)
            matches = list(match)
            if matches:
                final_answer = matches[-1].group(1).strip()
                final_answer = final_answer.replace('```dafny', '').strip()
                final_answer = final_answer.replace('```', '').strip()
                final_answer = final_answer.replace('<|im_start|>', '').strip()
            else:
                answer_pattern = r'```dafny(.*?)<\|im_end\|>'
                match = re.finditer(answer_pattern, solution_str, re.DOTALL)
                matches = list(match)
                if matches:
                    final_answer = matches[-1].group(1).strip()
                    final_answer = final_answer.replace('```dafny', '').strip()
                    final_answer = final_answer.replace('```', '').strip()
                    final_answer = final_answer.replace('<|im_start|>', '').strip()
                else:
                    final_answer = None
                # final_ansewr = final_answer.replace('<|im_end|>', '').strip()
    if final_answer is not None:
        another_match = re.finditer(r'(.*?)<\|im_end\|>', final_answer, re.DOTALL)
        matches = list(another_match)
        if matches:
            try:
                final_answer = matches[-1].group(1).strip()
            except Exception as e:
                final_answer = None
        else:
            final_answer = final_answer
    return final_answer

def tidy_dafny_code(dafny_code: str) -> str:
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

import os
import hashlib
import random
def execute(cmd, ext, v, timeout_sec = 10, HOME_DIR = 'trash'):
    TMP_DIR = f"{HOME_DIR}/tmp/llm-verified/{ext}/"
    # generate a random str of length 10 using {a,b,c,...}
    random_str = ''.join(random.choices('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=10))
    key = hashlib.md5(v.encode("utf-8")).hexdigest()
    key = key + random_str
    dir = "%s%s/" % (TMP_DIR, key)
    old_dir = os.getcwd()
    if not os.path.exists(dir):
        os.makedirs(dir)
    os.chdir(dir)

    try:
        fn = f"ex.{ext}"
        outfn = "out.txt"
        errfn = "err.txt"

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
    finally:
        os.chdir(old_dir)
    # remove new dir generated.
    os.system("rm -rf " + dir)

    return {"status": status, "log": log, "out": outlog}


def extract_tosearch(code, tosearch):
    """ Extracts assume statements from Dafny code """
    # This regular expression matches assume statements assuming they end with a semicolon
    assume_pattern = re.compile(tosearch)
    assumes = assume_pattern.findall(code)
    return set(assumes)

def check_no_cheat_by_less_ensure(complete_code, answer):
    # return True, None
    complete_ensures = extract_tosearch(complete_code,'ensures'+r' (.*?)\n')
    complete_ensures = [x.strip('{') for x in complete_ensures] 
    complete_ensures = [x.strip('}') for x in complete_ensures] 
    complete_ensures = [x.strip() for x in complete_ensures]    
    answer_ensures = extract_tosearch(answer,'ensures'+r' (.*?)\n')
    answer_ensures = [x.strip('{') for x in answer_ensures] # the tidy_up function might add additional { at the end of the 'ensures' line, so we have to remove them.
    answer_ensures = [x.strip('}') for x in answer_ensures] # the tidy_up function might add additional { at the end of the 'ensures' line, so we have to remove them.
    answer_ensures = [x.strip() for x in answer_ensures]    # the tidy_up function might add additional { at the end of the 'ensures' line, so we have to remove them.
    # for lines that contains annotation, like: ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of nonempty substrings of a string {, we need to remove the annotation part.
    complete_ensures = [x.split('//')[0].strip() for x in complete_ensures]
    answer_ensures = [x.split('//')[0].strip() for x in answer_ensures]
    
    if len(answer_ensures) == 0:
        return False, None
    else:
        return True, None

    # print(complete_ensures)
    # print(answer_ensures)
    
    # missing_ensures = [ensure for ensure in complete_ensures if ensure not in answer_ensures]
    # if len(missing_ensures) > 0:
    #     return False, missing_ensures
    # else:
    #     return True, None


def check_no_cheat_by_more_assume(complete_code, answer):
    return True, None
    # Extract assume statements from both pieces of code
    complete_assumes = extract_tosearch(complete_code,'assume'+r' (.*?);')
    answer_assumes = extract_tosearch(answer,'assume'+r' (.*?);')
    complete_assumes = [x.split('//')[0].strip() for x in complete_assumes]
    answer_assumes = [x.split('//')[0].strip() for x in answer_assumes]
    # print(complete_assumes)
    # print(answer_assumes)
    # Check if all assumes in the answer are in the complete code's assumes
    missing_assumes = [assume for assume in answer_assumes if assume not in complete_assumes]
    if len(missing_assumes) > 0:
        return False, missing_assumes
    else:
        return True, None


def extract_tosearch(code, tosearch):
    """ Extracts assume statements from Dafny code """
    # This regular expression matches assume statements assuming they end with a semicolon
    assume_pattern = re.compile(tosearch)
    assumes = assume_pattern.findall(code)
    return set(assumes)
def check_keywords_by_semicolon(complete_code, answer, keyword='assume'):
    complete_items = extract_tosearch(complete_code,keyword+r' (.*?);')
    answer_items = extract_tosearch(answer,keyword+r' (.*?);')
    complete_items = [x.split('//')[0].strip() for x in complete_items]
    answer_items = [x.split('//')[0].strip() for x in answer_items]

    items_only_in_answer = list(set(answer_items) - set(complete_items))
    items_only_in_gt = list(set(complete_items) - set(answer_items))
    items_in_common = list(set(complete_items) & set(answer_items))

    return dict(
        items_in_common=items_in_common,
        items_only_in_gt=items_only_in_gt,
        items_only_in_answer=items_only_in_answer,
    )
def check_no_cheat_by_less_assert(complete_code, answer):
    return True, None
    items_dict = check_keywords_by_semicolon(complete_code, answer, keyword='assert')
    if len(items_dict['items_only_in_gt']) > 0:
        return False, items_dict['items_only_in_gt']
    else:
        return True, None

def count_words(input_string):
    return len(input_string.split())

def compute_score(solution_str, ground_truth, method='strict',
    max_think_reward = 0.0, corresponding_max_think_length = 80, fail_execute_score = 0.01, compile_score=0.4, cheatby_less_ensures_score = 0.0, cheatby_more_assume_score=0.25, score=1.):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        method: the method to extract the solution
        compile_score: the score for correct format
        score: the score for the correct answer
    """
    
    complete_code = ground_truth['ground_truth']
    remhints_code = ground_truth['hints_removed']
    
    
    
    
    code = extract_solution(solution_str=solution_str)
    do_print = random.randint(1, 50) == 1
    
    if do_print:
        print(f"--------------------------------")
        print(f"Complete code: {complete_code}")
        print(f"Extracted code: {code}")
        print(f"Solution string: {solution_str}")
    
    if code is None:
        if do_print:
            print(f"No codestring found")
        return 0

    think_process = extract_think_process(solution_str=solution_str)
    think_length = count_words(think_process) if think_process is not None else 0
    think_score = min(think_length / corresponding_max_think_length, 1) * max_think_reward
    
    # print(code)

    if do_print:
        print(f"Think score for this response: {think_score}")
    
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30)
    # print(return_dict)
    

    if 'parse errors detected' in return_dict["out"]:
        if do_print:
            print("Execution result: Parse Errors Detected.")
        return fail_execute_score + think_score
    
    # successfully compiled
    
    tidied_code = tidy_dafny_code(code)
    
    if not check_no_cheat_by_less_ensure(complete_code, tidied_code)[0]:
        if do_print:
            print("Execution result: Parse Errors Not Detected. Cheat by less ensure.")
        
        return cheatby_less_ensures_score + think_score
    
    if '0 errors' in return_dict["out"]:
        # successfully executed
        # check for cheating
        if not check_no_cheat_by_more_assume(complete_code, tidied_code)[0]:
            if do_print:
                print("Execution result: Parse Errors Not Detected. Cheat by assume.")
            
            return cheatby_more_assume_score + think_score
        else:
            if do_print:
                print("Execution result: Parse Errors Not Detected. Successfully verified.")
            
            return score + think_score
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return compile_score + think_score



def compute_success_rate(solution_str, ground_truth, method='strict', fail_execute_score = 0.0, compile_score=0.0, cheatby_less_ensures_score = 0.0, cheatby_more_assume_score=0.0, score=1.):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        method: the method to extract the solution
        compile_score: the score for correct format
        score: the score for the correct answer
    """
    
    complete_code = ground_truth['ground_truth']
    remhints_code = ground_truth['hints_removed']
    
    
    
    
    code = extract_solution(solution_str=solution_str)
    do_print = random.randint(1, 50) == 1
    
    if do_print:
        print(f"--------------------------------")
        print(f"Complete code: {complete_code}")
        print(f"Extracted code: {code}")
        print(f"Solution string: {solution_str}")
    
    if code is None:
        if do_print:
            print(f"No codestring found")
        return 0
    
    # print(code)
    
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30)
    # print(return_dict)
    

    if 'parse errors detected' in return_dict["out"]:
        if do_print:
            print("Execution result: Parse Errors Detected.")
        return fail_execute_score
    
    # successfully compiled
    
    tidied_code = tidy_dafny_code(code)
    
    if not check_no_cheat_by_less_ensure(complete_code, tidied_code)[0]:
        if do_print:
            print("Execution result: Parse Errors Not Detected. Cheat by less ensure.")
        
        return cheatby_less_ensures_score
    
    if '0 errors' in return_dict["out"]:
        # successfully executed
        # check for cheating
        if not check_no_cheat_by_more_assume(complete_code, tidied_code)[0]:
            if do_print:
                print("Execution result: Parse Errors Not Detected. Cheat by assume.")
            
            return cheatby_more_assume_score
        else:
            if do_print:
                print("Execution result: Parse Errors Not Detected. Successfully verified.")
            
            return score
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return compile_score