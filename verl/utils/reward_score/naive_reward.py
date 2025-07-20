import re
import random
import ast
import operator
import difflib
import math
import time
from verl.utils.reward_score.condition_comparison_fixed import *

LOG_DIR = "/nas/shared/sys2/chefengdi/report_full_log_3/"
def is_fuzzy_match(original, modified):
    """
    验证 modified 是否是 original 插入若干行以及增加或减少空白字符后得到的。
    
    :param original: 原始字符串
    :param modified: 修改后的字符串
    :return: 如果 modified 是 original 的模糊匹配结果，则返回 True，否则返回 False
    """
    # 将字符串按行分割
    # original_lines = original.splitlines()
    original_lines = [line.strip() for line in original.splitlines()]
    # modified_lines = modified.splitlines()
    modified_lines = [line.strip() for line in modified.splitlines()]
    
    # 使用 difflib.Differ 比较字符串
    differ = difflib.Differ()
    diff = list(differ.compare(original_lines, modified_lines))
    
    # 检查差异
    for line in diff:
        if line.startswith('? '):  # 忽略空白字符的差异
            continue
        if line.startswith('- '):  # 原始字符串中有但修改后的字符串中没有的行
            return False
        if line.startswith('+ '):  # 修改后的字符串中有但原始字符串中没有的行
            continue  # 允许插入行
        if line.startswith('  '):  # 完全相同的行
            continue
    
    return True

def extract_input(solution_str):
    if "Assistant:" in solution_str:
        solution_str = solution_str.split("Assistant:", 1)[0]
    elif "<|im_start|>assistant" in solution_str:
        solution_str = solution_str.split("<|im_start|>assistant", 1)[0]
    else:
        return None

    solution_str = solution_str.split("Below is the program:")[1]
    # print("----------------------------")
    # print(solution_str)
    # print("----------------------------")

    think_pattern = r'```dafny(.*?)<\|im_end\|>'
    match = re.finditer(think_pattern, solution_str, re.DOTALL)
    matches = list(match)
    if matches:
        final_answer = matches[-1].group(1).strip()
        final_answer = final_answer.replace('```dafny', '')
        final_answer = final_answer.replace('```', '').strip()
    else:
        final_answer = None
    return final_answer

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
import time
def execute(cmd, ext, v, timeout_sec = 10, index=-1, exp_name = "exp"):
    # TMP_DIR = f"{HOME_DIR}/tmp/llm-verified/{ext}/"
    # exp_name = "exp"

    # start_time = time.time()

    dir = f"{LOG_DIR}/{exp_name}/{index}/"
    os.makedirs(dir, exist_ok=True)
    os.chdir(dir)
    # log_file = f"{LOG_DIR}/{exp_name}/{index}.dfy"
    # generate a random str of length 10 using {a,b,c,...}
    # random_str = ''.join(random.choices('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=10))
    # key = hashlib.md5(v.encode("utf-8")).hexdigest()
    # key = key + random_str
    # dir = "%s%s/" % (TMP_DIR, key)
    # old_dir = os.getcwd()
    # if not os.path.exists(dir):
    #     os.makedirs(dir)
    # os.chdir(dir)

    try:
        num_files = len(os.listdir(dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = f"{number}.dfy"
        outfn = f"out-{number}.txt"
        errfn = f"err-{number}.txt"

        f = open(fn, "w")
        f.write(v)
        f.close()

        # print("Disk time", time.time() - start_time)

        runcmd = "timeout --kill-after=5 %s %s %s >%s 2>%s" % (str(timeout_sec), cmd, fn, outfn, errfn)
        # if use_sandbox:
        #     if docker_sandbox:
        #         runcmd = 'docker run --rm --platform linux/amd64 -v "$(pwd):/app" namin/llm-verified ' + runcmd.replace(fn, "/app/"+fn)
        #     else:
        #         pre_llm_command = "singularity exec --no-mount=/n --no-mount=/net --no-mount=/scratch --no-mount=/cvmfs ~/singularity/llm-verified_latest.sif"
        #         runcmd = "SINGULARITY_HOME=/ timeout 10 %s %s %s >%s 2>%s" % (pre_llm_command, cmd, fn, outfn, errfn)

        #print("RUN CMD:", runcmd)
        status = os.system(runcmd)

        # print("Verifier Time:", time.time() - start_time)

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
        
        # print("Total Verifier Time:", time.time() - start_time)
    except:
        pass
    # finally:
    #     os.chdir(old_dir)
    # remove new dir generated.
    # os.system("rm -rf " + dir)

    return {"status": status, "log": log, "out": outlog}


def extract_tosearch(code, tosearch):
    """ Extracts assume statements from Dafny code """
    # This regular expression matches assume statements assuming they end with a semicolon
    assume_pattern = re.compile(tosearch)
    assumes = assume_pattern.findall(code)
    return set(assumes)

def no_only_ensures_equiv_for_any_method(complete_code):
    equiv_pattern = re.compile(r'\s*(\w+)\s*==\s*\1\s*')
    specs = extract_specs(complete_code)
    for key, value in specs.items():
        if len(value['ensures'])==1 and equiv_pattern.search(value["ensures"][0]):
            return False
    return True


def check_no_cheat(code):
    # check if there is any ensure:
    complete_ensures = extract_tosearch(code,'ensures'+r' (.*?)\n')
    if len(complete_ensures) == 0:
        print("hack by no ensure####")
        print(code)
        return False
    # true or false should not appear in the answer
    for ensure in complete_ensures:
        if "true" in ensure or "false" in ensure:
            print("hack by true or false####")
            print(code)
            return False
    # # ensure A==A makes no sense
    equal_ensures = extract_tosearch(code, 'ensures\s+(\w+)\s*==\s*\1\s*')
    if len(equal_ensures) > 0:
        print("hack by equal_ensures####")
        print(code)
        return False
    # # must not assume false
    # if "assume false" in code:
    #     print("hack by assume false####")
    #     print(code)
    #     return False
      
    return True
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

def check_no_cheat_by_ensure_true(complete_code):
    # return True, None
    complete_ensures = extract_tosearch(complete_code,'ensures'+r' (.*?)\n')
    for ensure in complete_ensures:
        if "true" in ensure or "false" in ensure:
            return False
    return True
        

def check_no_cheat_by_more_assume(complete_code, answer):
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

def find_num_ensures(input_string):
    complete_ensures = extract_tosearch(input_string,'ensures'+r' (.*?)\n')
    num_ensures = len(complete_ensures)
    return num_ensures

def compute_score(solution_str, ground_truth, exp_name, index, method='strict',
    max_think_reward = 0.0, corresponding_max_think_length = 80, fail_execute_score = 0.01, compile_score=0.2, cheatby_less_ensures_score = 0.0, cheatby_more_assume_score=0.25, score=0.8, num_examine=0):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        method: the method to extract the solution
        compile_score: the score for correct format
        score: the score for the correct answer
    """
    
    complete_code = ground_truth['ground_truth']   
    code = extract_solution(solution_str=solution_str)

    input_code = extract_input(solution_str=solution_str)
    if input_code is None:
        print(f"Solution string: {solution_str}")
        print("No input found")
        _dir = f"{LOG_DIR}/{exp_name}/{index}/"
        os.makedirs(_dir, exist_ok=True)
        os.chdir(_dir)
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = f"{number}.dfy"
        f = open(fn, "w")
        f.write("No input found")
        f.close()
        return (0, 0, 0)





    # do_print = random.randint(1, 500) == 1
    # if num_examine > 0:
    #     print("Validation result:")
    #     do_print = True
    # do_print = True
    do_print = False


    _dir = f"{LOG_DIR}/{exp_name}/{index}/"
    os.makedirs(_dir, exist_ok=True)

    if not os.path.exists(os.path.join(_dir, "gt.dfy")):
        fn = os.path.join(_dir, "gt.dfy")
        f = open(fn, "w")
        f.write(complete_code)
        f.close()

    if not os.path.exists(os.path.join(_dir, "input.dfy")):
        fn = os.path.join(_dir, "input.dfy")
        f = open(fn, "w")
        f.write(input_code)
        f.close()


    if code is None:
        if do_print:
            print(f"No codestring found")
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No output code found")
        f.close()
        return (0, 0, 0)


    num_gt_ensures = find_num_ensures(complete_code)
    num_ensures = find_num_ensures(code)


    if do_print:
        print(f"--------------------------------")
        print(f"num_gt_ensures: {num_gt_ensures}")
        print(f"num_ensures: {num_ensures}")
        print(f"Complete code: {complete_code}")
        print(f"Extracted code: {code}")
        print(f"Solution string: {solution_str}")
    if not is_fuzzy_match(input_code, code):
        # print("original code changed")     
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write(code)
        f.close()

        out_fn = os.path.join(_dir, f"out-{number}.txt")
        g = open(out_fn, "w")
        g.write("Original Code changed")
        g.close()
        return (0, 0, 0)
    think_process = extract_think_process(solution_str=solution_str)
    think_length = count_words(think_process) if think_process is not None else 0
    think_score = min(think_length / corresponding_max_think_length, 1) * max_think_reward
    
    # print(code)

    if do_print:
        print(f"Think score for this response: {think_score}")
    
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30, index=index, exp_name=exp_name)
    # print(return_dict)
    

    if 'parse errors detected' in return_dict["out"]:
        if do_print:
            print("Execution result: Parse Errors Detected.")
        return (fail_execute_score + think_score, 0, 0)
    

    if 'resolution/type error' in return_dict["out"]:
        if do_print:
            print("Execution result: Resolution/Type Error.")
        return (fail_execute_score + think_score, 0, 0)
    # successfully compiled
    
    if not check_no_cheat_by_ensure_true(code):
        print("Execution result: Parse Errors Not Detected. Cheat by ensure true.")
        return (0,0,0)

    if not no_only_ensures_equiv_for_any_method(code):
        print("Execution result: Parse Errors Not Detected. Cheat by only ensures equiv for any method.")
        return (0,0,0)
    
    no_cheat, _ = check_no_cheat_by_more_assume(complete_code, code)
    if not no_cheat:
        if do_print:
            print("Execution result: Parse Errors Not Detected. Cheat by more assume.")
        return (0,0,0)
    
    if ' 0 errors' in return_dict["out"]:
        return (compile_score + think_score + score , 0, 1)
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return (compile_score + think_score , 0, 0)

if __name__ == "__main__":
    solution_str = """
     <|im_start|>system
 You are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.
 <|im_end|>
 <|im_start|>user
 Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines.
         Show your middle progress in <think> </think> tags, And return the final answer in <answer>```dafny </answer> tags, DO NOT output you answer in <think></think>: return you answer in <ansewr></answer> tags. For example: <answer>```dafny method some_method ... ```</answer>. Below is the program: ```dafny
 
 datatype JsonData = JsonData(contents: seq<int>)
 datatype LoadResult = 
   | Success(data: JsonData)
   | FileNotFound 
   | NetworkError
 class FileSystem {
   var fileExists: map<string, bool>
   var fileContents: map<string, JsonData>
   constructor()
   {
     fileExists := map[];
     fileContents := map[];
   }
   method CheckExists(path: string) returns (b: bool)
   {
     if path in fileExists {
       return fileExists[path];
     }
     return false;
   }
   method ReadFile(path: string) returns (result: LoadResult)
   {
     if fileContents[path].contents == [] {
       return NetworkError;
     }
     return Success(fileContents[path]);
   }
 }
 method DownloadFromUrl(url: string) returns (result: LoadResult)
 {
   var contents := [1, 2, 3]; 
   return Success(JsonData(contents));
 }
 method Load(fs: FileSystem?) returns (result: LoadResult)
 {
   var fileExists := fs.CheckExists("path");
   
   if !fileExists {
     var downloadResult := DownloadFromUrl("url");
     if downloadResult.NetworkError? {
       return NetworkError;
     }
     if !downloadResult.Success? {
       return downloadResult;
     }
     
     fs.fileExists := fs.fileExists["path" := true];
     fs.fileContents := fs.fileContents["path" := downloadResult.data];
     return Success(downloadResult.data);
   } else {
     
     fs.fileContents := fs.fileContents["path" := JsonData([1,2,3])];
     var readResult := fs.ReadFile("path");
     if !readResult.Success? {
       return readResult;
     }
     return readResult;
   }
 }
 ```
 
 <|im_end|>
 <|im_start|>assistant
 Let me solve this step by step.
 <think> Well, 1st, Some errors came out.</think>
 ```dafny
 datatype JsonData = JsonData(contents: seq<int>)
 datatype LoadResult = 
   | Success(data: JsonData)
   | FileNotFound 
   | NetworkError
 class FileSystem {
   var fileExists: map<string, bool>
   var fileContents: map<string, JsonData>
   constructor()
     ensures fresh(this)
     ensures fileExists == map[]
     ensures fileContents == map[]
   {
     fileExists := map[];
     fileContents := map[];
   }
   method CheckExists(path: string) returns (b: bool)
     ensures b <==> path in fileExists && fileExists[path]
     ensures path !in fileExists ==> !b
   {
     if path in fileExists {
       return fileExists[path];
     }
     return false;
   }
   method ReadFile(path: string) returns (result: LoadResult)
     requires path in fileContents
     ensures result.Success? ==> result.data == fileContents[path]
     ensures fileContents[path].contents == [] ==> result.NetworkError?
   {
     if fileContents[path].contents == [] {
       return NetworkError;
     }
     return Success(fileContents[path]);
   }
 }
 method DownloadFromUrl(url: string) returns (result: LoadResult)
   ensures result.Success? ==> result.data.contents != []
   ensures result.NetworkError? ==> result == NetworkError
 {
   var contents := [1, 2, 3]; 
   return Success(JsonData(contents));
 }
 method Load(fs: FileSystem?) returns (result: LoadResult)
   requires fs != null
   modifies fs
   ensures result.Success? ==> "path" in fs.fileExists && fs.fileExists["path"]
   ensures result.Success? ==> "path" in fs.fileContents && fs.fileContents["path"].contents == result.data.contents
 {
   var fileExists := fs.CheckExists("path");
   
   if !fileExists {
     var downloadResult := DownloadFromUrl("url");
     if downloadResult.NetworkError? {
       return NetworkError;
     }
     if !downloadResult.Success? {
       return downloadResult;
     }
     
     fs.fileExists := fs.fileExists["path" := true];
     fs.fileContents := fs.fileContents["path" := downloadResult.data];
     return Success(downloadResult.data);
   } else {
     
     fs.fileContents := fs.fileContents["path" := JsonData([1,2,3])];
     var readResult := fs.ReadFile("path");
     if !readResult.Success? {
       return readResult;
     }
     return readResult;
   }
 }
 ```
 
 <|im_end|>
    """
    ground_truth = {}
    ground_truth['ground_truth'] = """
```dafny
 datatype JsonData = JsonData(contents: seq<int>)
 datatype LoadResult = 
   | Success(data: JsonData)
   | FileNotFound 
   | NetworkError
 class FileSystem {
   var fileExists: map<string, bool>
   var fileContents: map<string, JsonData>
   constructor()
     ensures fresh(this)
     ensures fileExists == map[]
     ensures fileContents == map[]
   {
     fileExists := map[];
     fileContents := map[];
   }
   method CheckExists(path: string) returns (b: bool)
     ensures b <==> path in fileExists && fileExists[path]
   {
     if path in fileExists {
       return fileExists[path];
     }
     return false;
   }
   method ReadFile(path: string) returns (result: LoadResult)
     requires path in fileExists && fileExists[path]
     requires path in fileContents
     ensures result.Success? ==> result.data == fileContents[path]
     ensures result.Success? ==> result.data.contents != []
   {
     if fileContents[path].contents == [] {
       return NetworkError;
     }
     return Success(fileContents[path]);
   }
 }
 method DownloadFromUrl(url: string) returns (result: LoadResult)
   ensures result.Success? ==> result.data.contents != []
 {
   var contents := [1, 2, 3]; 
   return Success(JsonData(contents));
 }
 method Load(fs: FileSystem?) returns (result: LoadResult)
   requires fs != null
   ensures result.Success? ==> result.data.contents != []
   modifies fs
 {
   var fileExists := fs.CheckExists("path");
   
   if !fileExists {
     var downloadResult := DownloadFromUrl("url");
     if downloadResult.NetworkError? {
       return NetworkError;
     }
     if !downloadResult.Success? {
       return downloadResult;
     }
     
     fs.fileExists := fs.fileExists["path" := true];
     fs.fileContents := fs.fileContents["path" := downloadResult.data];
     return Success(downloadResult.data);
   } else {
     assert "path" in fs.fileExists && fs.fileExists["path"];
     
     fs.fileContents := fs.fileContents["path" := JsonData([1,2,3])];
     assert "path" in fs.fileContents;
     var readResult := fs.ReadFile("path");
     if !readResult.Success? {
       return readResult;
     }
     return readResult;
   }
 }
    """
    compute_score(solution_str, ground_truth, method='strict',
    max_think_reward = 0.0, corresponding_max_think_length = 80, fail_execute_score = 0.01, compile_score=0.4, cheatby_less_ensures_score = 0.0, cheatby_more_assume_score=0.25, score=1.)