import re
import random
import ast
import operator
import difflib
import math
import os
import hashlib
    
    
    
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

def extract_tosearch(code, tosearch):
    """ Extracts assume statements from Dafny code """
    # This regular expression matches assume statements assuming they end with a semicolon
    assume_pattern = re.compile(tosearch)
    assumes = assume_pattern.findall(code)
    return set(assumes)