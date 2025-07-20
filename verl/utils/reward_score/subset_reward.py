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
from verl.utils.reward_score.condition_comparison_fixed import *
from verl.inference.reward_score.inference_reward import reinsert_gt_spec
from verl.inference.reward_score.spec_coverage import analyze_spec_coverage
from concurrent.futures import ThreadPoolExecutor, as_completed

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

LOG_DIR = "logs/"

def count_words(input_string):
    return len(input_string.split())

def find_num_ensures(input_string):
    complete_ensures = extract_tosearch(input_string,'ensures'+r' (.*?)\n')
    num_ensures = len(complete_ensures)
    return num_ensures

def execute(cmd, ext, v, timeout_sec = 10, index=-1, exp_name = "exp"):
    # TMP_DIR = f"{HOME_DIR}/tmp/llm-verified/{ext}/"
    # exp_name = "exp"
    dir = f"{LOG_DIR}/{exp_name}/{index}/"
    os.makedirs(dir, exist_ok=True)
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
    except Exception as e:
        num_files = len(os.listdir(dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(dir, f"{number}.dfy") 
        outfn = os.path.join(dir, f"out-{number}.txt")
        errfn = os.path.join(dir, f"err-{number}.txt")

        f = open(fn, "w")
        f.write("Unknown error in execution: " + str(e))
        f.close()
        pass
    # finally:
    #     os.chdir(old_dir)
    # remove new dir generated.
    # os.system("rm -rf " + dir)

    return {"status": status, "log": log, "out": outlog}

def execute_diff_location(cmd, ext, v, timeout_sec = 10, index=-1, exp_name = "exp",name=None):
    if name is None:
        name = "specRefine"
    dir = f"{LOG_DIR}/{exp_name}/{index}/{name}"
    os.makedirs(dir, exist_ok=True)

    try:
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
    except:
        pass

    return {"status": status, "log": log, "out": outlog}


def no_only_ensures_equiv_for_any_method(complete_code):
    equiv_pattern = re.compile(r'\s*(\w+)\s*==\s*\1\s*')
    specs = extract_specs(complete_code)
    for key, value in specs.items():
        if len(value['ensures'])==1 and equiv_pattern.search(value["ensures"][0]):
            return False
    return True

def check_no_cheat_by_ensure_true(complete_code):
    # return True, None
    complete_ensures = extract_tosearch(complete_code,r'ensures\s+(true|false)')
    if len(complete_ensures) != 0:
        return False
    return True

def compute_score(solution_str, 
                  ground_truth, 
                  exp_name, 
                  index, 
                  method='strict',
                  max_think_reward = 0.0, 
                  corresponding_max_think_length = 80, 
                  fail_execute_score = 0.01, 
                  compile_score=0.2, 
                  score=0.4, 
                  refine_score=0.4, 
                  num_examine=0, 
                  version="one_score"):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        method: the method to extract the solution
        compile_score: the score for correct format
        score: the score for the verifiable answer
    """
    
    complete_code = ground_truth['ground_truth']   
    code = extract_solution(solution_str=solution_str)
    input_code = extract_input(solution_str=solution_str)

    # code = solution_str
    # complete_code = ground_truth[0]
    # input_code = ground_truth[1]

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

    if input_code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No input found")
        f.close()
        print(f"Solution string: {solution_str}")
        print("No input found")
        return (0,0,0)
    

    # do_print = random.randint(1, 500) == 1
    # if num_examine > 0:
    #     print("Validation result:")
    #     do_print = True
    # do_print = True
    do_print = False

    if code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No codestring found")
        f.close()
        if do_print:
            print(f"No codestring found")
        return (0,0,0)

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
        # print(code)
        # print(input_code)
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No output code found")
        f.close()
        print("original code changed")
        return (0,0,0)
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
        return (fail_execute_score , 0, 0)
    

    if 'resolution/type error' in return_dict["out"]:
        if do_print:
            print("Execution result: Resolution/Type Error.")
        return (fail_execute_score , 0, 0)
    # successfully compiled
    
    counts,count = count_members(code)
    
    # if version != "prevent_hacking":
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

    value = 0
    
    if ' 0 errors' in return_dict["out"]:
        try: 
            output_file = os.path.join(_dir, "extract")
            new_dafny = strip_specs_and_inject_asserts(complete_code, code, key="one_score",output_file=output_file)
            one_score_dict = execute_diff_location("dafny verify", "dfy", new_dafny, timeout_sec=30, index=index, exp_name=exp_name)
            
            if check_parse_errors(one_score_dict):
                value = 0
            else:
                errors = one_score_dict["out"].count("assertion might not hold")
                func_errors = one_score_dict["out"].count("a postcondition could not be proved on this return path")
                strong = errors==0
                func_strong = func_errors==0
                if new_dafny.count("assert")>0 or new_dafny.count("ensures")>0:
                    value = int(strong * func_strong)
                else:
                    value = 0
        except Exception as e:
            print(f"{bcolors.WARNING}An error occurred! {bcolors.ENDC}")
            print("An error occurred:", e)
            # print(code)
            print("#"*30)
            value = 0
        # spec_dir = f"{LOG_DIR}/{exp_name}/{index}/spec_coverage"
        # _, ensures_cov = analyze_spec_coverage(complete_code, code, spec_dir)
        # if ensures_cov == 1.0:
        #     value = refine_score
        return (compile_score + score + value, value/refine_score, 1)
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return (compile_score + think_score+ value, value/refine_score, 0)

def compute_intermediate_score(solution_str, 
                  ground_truth, 
                  exp_name, 
                  index, 
                  method='strict',
                  max_think_reward = 0.0, 
                  corresponding_max_think_length = 80, 
                  fail_execute_score = 0.01, 
                  compile_score=0.2, 
                  score=0.4, 
                  refine_score=0.4, 
                  num_examine=0, 
                  version="no_hacking"):
    """The scoring function for countdown task.
    
    Args:
        solution_str: the solution text
        ground_truth: dictionary containing target number and available numbers
        method: the method to extract the solution
        compile_score: the score for correct format
        score: the score for the verifiable answer
    """
    
    complete_code = ground_truth['ground_truth']   
    code = extract_solution(solution_str=solution_str)
    input_code = extract_input(solution_str=solution_str)

    # code = solution_str
    # complete_code = ground_truth[0]
    # input_code = ground_truth[1]

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

    if input_code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No input found")
        f.close()
        print(f"Solution string: {solution_str}")
        print("No input found")
        return (0,0,0)
    

    # do_print = random.randint(1, 500) == 1
    # if num_examine > 0:
    #     print("Validation result:")
    #     do_print = True
    # do_print = True
    do_print = False

    if code is None:
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No codestring found")
        f.close()
        if do_print:
            print(f"No codestring found")
        return (0,0,0)

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
        # print(code)
        # print(input_code)
        num_files = len(os.listdir(_dir))
        number = num_files * 10000 + random.randint(0, 9999)
        fn = os.path.join(_dir, f"{number}.dfy")
        f = open(fn, "w")
        f.write("No output code found")
        f.close()
        print("original code changed")
        return (0,0,0)
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
        return (fail_execute_score , 0, 0)
    

    if 'resolution/type error' in return_dict["out"]:
        if do_print:
            print("Execution result: Resolution/Type Error.")
        return (fail_execute_score , 0, 0)
    # successfully compiled
    
    counts,count = count_members(code)
    
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
    try:
        gt_insert_code = reinsert_gt_spec(complete_code, code) 
        intermediate_dict = execute_diff_location("dafny verify", "dfy", gt_insert_code, timeout_sec=30, index=index, exp_name=exp_name, name="intermediate")
        if not check_parse_errors(intermediate_dict) and ' 0 errors' in intermediate_dict["out"]:
            value = refine_score
        else:
            value = 0
    except Exception as e:
        print(f"{bcolors.WARNING}An error occurred! {bcolors.ENDC}")
        print("An error occurred:", e)
        # print(code)
        print("#"*30)
        value = 0

    if ' 0 errors' in return_dict["out"]:
        return (compile_score + think_score + score + value, value/refine_score, 1)
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return (compile_score + think_score + value, value/refine_score, 0)



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
   {
     if path in fileExists {
       return fileExists[path];
     }
     return false;
   }
   method ReadFile(path: string) returns (result: LoadResult)
     requires path in fileExists && fileExists[path]
     requires path in fileContents
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
    r = compute_score(solution_str, ground_truth,exp_name = 'exp',index=100, method='strict',
    max_think_reward = 0.0, corresponding_max_think_length = 80, fail_execute_score = 0.01, compile_score=0.4, score=0.4, requires_score = 0.2, ensures_score=1.0, num_examine=0, version="requires")
    print(r)