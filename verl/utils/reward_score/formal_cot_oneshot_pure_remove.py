import re
import random
import ast
import operator
import difflib, hashlib, os
import math
import time

from verl.utils.reward_score.naive_reward import *
from verl.utils.reward_score.subset_reward import execute_diff_location,execute
from verl.utils.reward_score.subset_reward import *
from verl.utils.reward_score.condition_comparison_fixed import *
from verl.inference.reward_score.spec_coverage import analyze_spec_coverage

LOG_DIR = "/nas/shared/sys2/chefengdi/report_full_log_3/"


def format_reward(solution_str: str):
    solution_str = solution_str.split("<|im_start|>assistant", 1)[1]
    # First find the position of first <|im_end|> to limit our search
    im_end_pos = solution_str.find("<|im_end|>")
    if im_end_pos == -1:
        im_end_pos = len(solution_str)
    
    # Get the substring before <|im_end|>
    search_str = solution_str[:im_end_pos]

    pattern = r"^\n*(\s*)<think>.*?</think><answer>.*?</answer>(\s*)\n*$"
    match = re.search(pattern, search_str, re.DOTALL | re.MULTILINE)
    return 1.0 if match is not None else 0.0 


def tag_count_reward(solution_str: str) -> list[float]:
    """Reward function that checks if we produce the desired number of think and answer tags associated with `format_reward()`.

    Adapted from: https://gist.github.com/willccbb/4676755236bb08cab5f4e54a0475d6fb#file-grpo_demo-py-L90
    """
    count = 0.0
    if solution_str.count("<think>") == 1:
        count += 0.25
    if solution_str.count("</think>") == 1:
        count += 0.25
    if solution_str.count("<answer>") == 1:
        count += 0.25
    if solution_str.count("</answer>") == 1:
        count += 0.25
    return count

def formal_reasoning_reward(think_code,index,exp_name):
    """Reward function that checks for syntax correctness of the thinking process.
    """
    if think_code is None:
      return 0.0

    if think_code.strip() == "":
      return 0.0

    return_dict = execute_diff_location("dafny verify", "dfy", think_code, timeout_sec=30, index=index, exp_name=exp_name)
    # print(return_dict)

    if 'parse errors detected' in return_dict["out"]:
      if '1 parse' in return_dict["out"] or '2 parse' in return_dict["out"] or '3 parse' in return_dict["out"]:
        return 1.0
      elif '4 parse' in return_dict["out"] or '5 parse' in return_dict["out"]:
        return 0.4
      print(return_dict["out"])
      return 0.0

    if 'resolution/type error' in return_dict["out"]:
      return 0.0

    # successfully compiled
    return 1.0


def cot_format_reward(think_code):
    """Reward function that checks for intermediate clauses only in the format of the reasoning.
    Each line should start with either clauses, titles, braces, structures, vars or lines without semi-colons.
    """

    if think_code is None:
      return 0.0
    
    SPECIAL_KEYWORDS = ['requires', 'ensures', 'invariant', 'assert','modifies', 
                    'assume', 'reads', 'decreases', 'reveal','while', 'if', 'else', 'match', 'then', 
                    'function','ghost','two_state','method','class', 'predicate','forall', 
                    'exists', 'yields', 'yield', 'return', 'var']

    lines = think_code.splitlines(keepends=True)
    semi_re   = re.compile(r';\s*$')

    symbols = ['==>','<==','==','&&','||']
    inline = False

    for line in lines:
        stripped = line.strip()
        if inline and any(stripped.endswith(symbol) for symbol in symbols):
            continue
        elif inline:
            inline=False
            continue
        if any(stripped.endswith(symbol) for symbol in symbols) or stripped in SPECIAL_KEYWORDS:
            inline = True

        # skip blank lines or braces
        if not stripped or stripped in ('{', '}'):
            continue
        
        # skip lines that begin with any SPECIAL_KEYWORDS
        first_tok = stripped.split()[0]
        if first_tok in SPECIAL_KEYWORDS:
            continue
        
        # skip lines that do not end with a right brace
        if not semi_re.search(line):
            continue
        
        return 0.0

    return 1.0

def extract_think_process(solution_str):
    if "Assistant:" in solution_str:
        solution_str = solution_str.split("Assistant:", 1)[1]
    elif "<|im_start|>assistant" in solution_str:
        solution_str = solution_str.split("<|im_start|>assistant", 1)[1]
    else:
        return None
    
    # Find content between first <think> and </think>
    think_pattern = r'<think>(.*?)</think>'
    match = re.finditer(think_pattern, solution_str, re.DOTALL)
    matches = list(match)
    if matches:
        final_answer = matches[-1].group(1).strip()

        final_answer = final_answer.replace('```dafny', '').strip()
        final_answer = final_answer.replace('```', '').strip()
        final_answer = final_answer.replace('<|im_start|>', '').strip()
        return final_answer
    return None



def compute_score(solution_str, 
                ground_truth, 
                exp_name, index, 
                method='strict',
                think_score_total = 0.2, 
                corresponding_max_think_length = 40, 
                fail_execute_score = 0.01, 
                compile_score=0.2, 
                score=0.6, 
                num_examine=0,
                version="parse_only",
                ):
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
    weight = min(think_length / corresponding_max_think_length, 1) 
    # weight =1 

    format_score, formal_reasoning_score = format_reward(solution_str), formal_reasoning_reward(think_process, index,exp_name)
    # format_score, formal_reasoning_score = cot_format_reward(think_process), formal_reasoning_reward(think_process, index,exp_name)
    think_score = (formal_reasoning_score) * think_score_total * weight
    # this one is for version=="only_parse"

    if version=="with_format" and think_process is not None:
        think_score = (format_score*0.5 + formal_reasoning_score*1.5) * think_score_total * weight
    
    # print(code)

    if do_print:
        print(f"Think score for this response: {think_score}")
        
    
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30, index=index, exp_name=exp_name)
    # print(return_dict)
    if 'parse errors detected' in return_dict["out"]:
        if do_print:
            print("Execution result: Parse Errors Detected.")
        return (fail_execute_score+think_score, think_score/think_score_total, 0)
    

    if 'resolution/type error' in return_dict["out"]:
        if do_print:
            print("Execution result: Resolution/Type Error.")
        return (fail_execute_score+think_score, think_score/think_score_total, 0)
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

    if ' 0 errors' in return_dict["out"]:
        return (compile_score + score + think_score, think_score/think_score_total, 1)
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return (compile_score + think_score, think_score/think_score_total, 0)

def compute_spec_score(solution_str, 
                ground_truth, 
                exp_name, index, 
                method='strict',
                think_score_total = 0.2, 
                corresponding_max_think_length = 40, 
                fail_execute_score = 0.01, 
                compile_score=0.2, 
                score=0.4, 
                refine_score=0.4,
                num_examine=0,
                version="with_format",
                ):
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
    weight = min(think_length / corresponding_max_think_length, 1) 
    # weight =1 

    format_score, formal_reasoning_score = format_reward(solution_str), formal_reasoning_reward(think_process, index,exp_name)
    # format_score, formal_reasoning_score = cot_format_reward(think_process), formal_reasoning_reward(think_process, index,exp_name)
    think_score = (formal_reasoning_score) * think_score_total * weight
    # this one is for version=="only_parse"

    if version=="with_format" and think_process is not None:
        think_score = (format_score*0.25 + formal_reasoning_score*0.75) * think_score_total * weight
    
    # print(code)

    if do_print:
        print(f"Think score for this response: {think_score}")
        
    
    return_dict = execute("dafny verify", "dfy", code, timeout_sec=30, index=index, exp_name=exp_name)
    # print(return_dict)
    if 'parse errors detected' in return_dict["out"]:
        if do_print:
            print("Execution result: Parse Errors Detected.")
        return (fail_execute_score+think_score, think_score/think_score_total, 0)
    

    if 'resolution/type error' in return_dict["out"]:
        if do_print:
            print("Execution result: Resolution/Type Error.")
        return (fail_execute_score+think_score, think_score/think_score_total, 0)
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
    # try: 
    #     new_dafny = strip_specs_and_inject_asserts(complete_code, code, key="one_score")
    #     one_score_dict = execute_diff_location("dafny verify", "dfy", new_dafny, timeout_sec=30, index=index, exp_name=exp_name)
        
    #     if check_parse_errors(one_score_dict):
    #         value = 0
    #     else:
    #         errors = one_score_dict["out"].count("assertion might not hold")
    #         strong = errors==0
    #         value = refine_score * strong
    # except Exception as e:
    #     print(f"{bcolors.WARNING}An error occurred! {bcolors.ENDC}")
    #     print("An error occurred:", e)
    #     # print(code)
    #     print("#"*30)
    #     value = 0
    
    value = 0
    if ' 0 errors' in return_dict["out"]:
        spec_dir = f"{LOG_DIR}/{exp_name}/{index}/spec_coverage"
        _, ensures_cov = analyze_spec_coverage(complete_code, code, spec_dir)
        if ensures_cov == 1.0:
            value = refine_score
        return (compile_score + score + value + think_score, value/refine_score, 1)
    else:
        if do_print:
            if (return_dict["status"] != 35072) and (return_dict["status"] != 31744):
                print("Execution result: Parse Errors Not Detected. Failed to be verified.")
            else:
                print("Execution result: Parse Errors Not Detected (likely not detected since out of time limit). Failed due to time limit.")
        # error in execution.
        return (compile_score + think_score+ value, value/refine_score, 0)
    


if __name__ == "__main__":
    solution_str = """
     <|im_start|>system
<|im_end|>
<|im_start|>user
You are given a Dafny program with functions and implementations, but no specification clauses. Only in <think>…</think>, reason in valid Dafny code with intermediate specification constructs (e.g. loop invariants, decreases clauses, assert statements, ghost code, helper lemmas, modifies clauses). Only in <answer>...</answer>, output the complete Dafny module, preserving all function signatures and lemma declarations exactly. Add the weakest requires and strongest ensures that allow the verifier to succeed, and fully characterize the code’s behavior, along with other necessary intermediate specifications from your `<think>` section. If you need to revise your reasoning, rewrite necessary functions in the think process as new ones whose names embed the original so think section gives no parse error, rather than patching individual lines. Do not ever modify the given lines. Never introduce any assume clauses. Output nothing outside the tags. Below is the program:
```dafny

class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
{
  matrices := map[];
  var l := 1;
  while l <= lag
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
      {
        if i - j >= 0 {
          var value: real;
          if t < season {
            value := 0.5 + 0.5 * SinApprox(t as real);
          } else {
            value := 0.5;
          }
          upstreamMap := upstreamMap[i-j := value];
        }
        j := j + 1;
      }
      if |upstreamMap| > 0 {
        reservoirMap := reservoirMap[i := upstreamMap];
      }
      i := i + 1;
    }
    matrices := matrices[l := reservoirMap];
    l := l + 1;
  }
}
``````<|im_end|>
<|im_start|>assistant
<think>method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
{
  var l := 1;
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
        }
      }
      }
    }
  }
</think><answer>```dafny
class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
    requires |ar| > 0 && |inflows| > 0
    requires forall i :: 0 <= i < |ar| ==> i in ar.Keys
    requires forall i, j :: 0 <= i < |ar| && j in ar[i] ==> j in ar[i].Keys
    requires forall i, j, k :: 0 <= i < |ar| && j in ar[i] && k in ar[i][j] ==> k in ar[i][j].Keys
    requires noise.Length0 > 0 && noise.Length1 > 0 && noise.Length2 > 0
    ensures matrices == ar
    ensures initialInflows == inflows
    ensures noiseMatrix == noise
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
  requires min < max
  ensures min <= r <= max
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
  requires numReservoirs > 0 && upStreamDep >= 0 && lag > 0
  requires t >= 0 && season > 0
  ensures |matrices| <= lag + 1
  ensures forall i :: 0 <= i < |matrices| ==> i in matrices.Keys
{
  matrices := map[];
  var l := 1;
  
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
          if t < season {
            
            value := 0.5 + 0.5 * SinApprox(t as real);
          } else {
            value := 0.5;
          }
          upstreamMap := upstreamMap[i-j := value];
        }
        j := j + 1;
      }
      if |upstreamMap| > 0 {
        reservoirMap := reservoirMap[i := upstreamMap];
      }
      i := i + 1;
    }
    matrices := matrices[l := reservoirMap];
    l := l + 1;
  }
}
```</answer><|im_end|>
<|im_end|>
<think>method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
{
  var l := 1;
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
        }
      }
      }
    }
  }
</think><answer>```dafny
class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
    requires |ar| > 0 && |inflows| > 0
    requires forall i :: 0 <= i < |ar| ==> i in ar.Keys
    requires forall i, j :: 0 <= i < |ar| && j in ar[i] ==> j in ar[i].Keys
    requires forall i, j, k :: 0 <= i < |ar| && j in ar[i] && k in ar[i][j] ==> k in ar[i][j].Keys
    requires noise.Length0 > 0 && noise.Length1 > 0 && noise.Length2 > 0
    ensures matrices == ar
    ensures initialInflows == inflows
    ensures noiseMatrix == noise
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
  requires min < max
  ensures min <= r <= max
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
  requires numReservoirs > 0 && upStreamDep >= 0 && lag > 0
  requires t >= 0 && season > 0
  ensures |matrices| <= lag + 1
  ensures forall i :: 0 <= i < |matrices| ==> i in matrices.Keys
{
  matrices := map[];
  var l := 1;
  
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
          if t < season {
            
            value := 0.5 + 0.5 * SinApprox(t as real);
          } else {
            value := 0.5;
          }
          upstreamMap := upstreamMap[i-j := value];
        }
        j := j + 1;
      }
      if |upstreamMap| > 0 {
        reservoirMap := reservoirMap[i := upstreamMap];
      }
      i := i + 1;
    }
    matrices := matrices[l := reservoirMap];
    l := l + 1;
  }
}
```</answer><|im_end|>
<|im_end|>
<think>method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
{
  var l := 1;
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
        }
      }
      }
    }
  }
</think><answer>```dafny
class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
    requires |ar| > 0 && |inflows| > 0
    requires forall i :: 0 <= i < |ar| ==> i in ar.Keys
    requires forall i, j :: 0 <= i < |ar| && j in ar[i] ==> j in ar[i].Keys
    requires forall i, j, k :: 0 <= i < |ar| && j in ar[i] && k in ar[i][j] ==> k in ar[i][j].Keys
    requires noise.Length0 > 0 && noise.Length1 > 0 && noise.Length2 > 0
    ensures matrices == ar
    ensures initialInflows == inflows
    ensures noiseMatrix == noise
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
  requires min < max
  ensures min <= r <= max
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
  requires numReservoirs > 0 && upStreamDep >= 0 && lag > 0
  requires t >= 0 && season > 0
  ensures |matrices| <= lag + 1
  ensures forall i :: 0 <= i < |matrices| ==> i in matrices.Keys
{
  matrices := map[];
  var l := 1;
  
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
          if t < season {
            
            value := 0.5 + 0.5 * SinApprox(t as real);
          } else {
            value := 0.5;
          }
          upstreamMap := upstreamMap[i-j := value];
        }
        j := j + 1;
      }
      if |upstreamMap| > 0 {
        reservoirMap := reservoirMap[i := upstreamMap];
      }
      i := i + 1;
    }
    matrices := matrices[l := reservoirMap];
    l := l + 1;
  }
}
```</answer><|im_end|>
<|im_end|>
<think>method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
{
  var l := 1;
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
        }
      }
      }
    }
  }
</think><answer>```dafny
class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
    requires |ar| > 0 && |inflows| > 0
    requires forall i :: 0 <= i < |ar| ==> i in ar.Keys
    requires forall i, j :: 0 <= i < |ar| && j in ar[i] ==> j in ar[i].Keys
    requires forall i, j, k :: 0 <= i < |ar| && j in ar[i] && k in ar[i][j] ==> k in ar[i][j].Keys
    requires noise.Length0 > 0 && noise.Length1 > 0 && noise.Length2 > 0
    ensures matrices == ar
    ensures initialInflows == inflows
    ensures noiseMatrix == noise
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
  requires min < max
  ensures min <= r <= max
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
  requires numReservoirs > 0 && upStreamDep >= 0 && lag > 0
  requires t >= 0 && season > 0
  ensures |matrices| <= lag + 1
  ensures forall i :: 0 <= i < |matrices| ==> i in matrices.Keys
{
  matrices := map[];
  var l := 1;
  
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant
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
    r = compute_score(solution_str, ground_truth, method='strict',exp_name='test', index=100)
    print(f"score: {r}")