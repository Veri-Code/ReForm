from openai import OpenAI
from tqdm import tqdm
from smart_open import open
import boto3
import os
from dataclasses import dataclass
from typing import Optional
import re


def init_generate_messages(python_code):
    """Original function for single-step conversion"""
    return [
        {
            "role": "system",
            "content": "You are an expert AI assistant that writes Dafny programs. You excel at writing code with formally verified correctness, providing precise preconditions and postconditions, and finding the appropriate loop invariants to ensure all verification conditions are met.",
        },
        {
            "role": "user",
            "content": "Here is some Python code:\n\n"
            + python_code
            + "\n\nPlease translate this Python code into Dafny, ensuring:\n\n1. **Method Signatures**: Each piece of functionality should be expressed as a Dafny method (or set of methods) with a well-defined signature.\n\n2. **Preconditions**: Clearly state any `requires` clauses for each method (e.g., array length constraints, non-null references, numeric domain restrictions, etc.).\n\n3. **Postconditions**: State the logical guarantees about the returned values or final state as `ensures` clauses (e.g., correctness of returned results, absence of side effects, etc.).\n\n4. **Verification Details**: Include all necessary loop invariants (or other verification hints) so Dafny can prove the postconditions, along with a brief explanation. For example:\n   - Explain how you chose your invariants.\n   - Describe how they ensure the correctness of the loop.\n\nReturn the final Dafny code as a self-contained snippet that can be verified by Dafny as-is, with a short explanation of how it connects to the original Python functionality.",
        },
    ]


def debug_messages(dafny_code, python_code, dafny_analysis_result):
    """Original debug function for single-step conversion"""
    return [
        {
            "role": "system",
            "content": "You are an expert AI assistant that writes and debugs Dafny programs. You excel at diagnosing and fixing verification errors based on Dafny solver messages, while maintaining correct preconditions, postconditions, and loop invariants."
        },
        {
            "role": "user",
            "content": "Below is the Python code:\n\n```python\n"
            + python_code
            + "\n```\n\nAnd the Dafny code you previously provided (which I tried to verify):\n\n```dafny\n"
            + dafny_code
            + "\n```\n\nI ran `dafny verify ***.dfy` and received this error message:\n\n```\n"
            + dafny_analysis_result
            + "\n```\n\nCan you please fix the code so that it verifies successfully? Output the final Dafny code only, without any other text.",
        },
    ]


def create_minimal_dafny_file(main_spec):
    """Create a minimal Dafny file for testing main specification"""
    return f"""// Minimal Dafny file for testing main function specification
{main_spec}
"""


def verify_main_spec(result_save_dir, dafny_bin_path, main_spec, iteration=None):
    """Verify main function specification with minimal Dafny file"""
    if iteration is None:
        iteration = "main_spec"
    
    # Create minimal Dafny file
    minimal_dafny = create_minimal_dafny_file(main_spec)
    dafny_code_path = f"{result_save_dir}/main_spec_{iteration}.dfy"
    open(dafny_code_path, "w").write(minimal_dafny)

    dafny_analysis_path = f"{result_save_dir}/main_spec_{iteration}.dfy.analysis"
    cmd = f"{dafny_bin_path} verify {dafny_code_path} --verbose >> {dafny_analysis_path}"
    os.system(cmd)

    return open(dafny_analysis_path, "r").read()


def identify_main_functions(python_code):
    """Identify functions that start with 'def main_' in the Python code"""
    main_functions = []
    lines = python_code.split('\n')
    
    for i, line in enumerate(lines):
        line = line.strip()
        if line.startswith('def main_'):
            # Extract function name and signature - handle different formats
            # Pattern 1: def func_name(param) -> return_type:
            match1 = re.match(r'def\s+(\w+)\s*\((.*?)\)\s*->\s*(.*?):', line)
            # Pattern 2: def func_name(param):
            match2 = re.match(r'def\s+(\w+)\s*\((.*?)\):', line)
            
            if match1:
                func_name = match1.group(1)
                params = match1.group(2)
                return_type = match1.group(3)
                main_functions.append({
                    'name': func_name,
                    'params': params,
                    'return_type': return_type,
                    'line_number': i + 1,
                    'full_line': line
                })
            elif match2:
                func_name = match2.group(1)
                params = match2.group(2)
                return_type = "object"  # Default return type
                main_functions.append({
                    'name': func_name,
                    'params': params,
                    'return_type': return_type,
                    'line_number': i + 1,
                    'full_line': line
                })
    
    return main_functions


def init_generate_main_spec_messages(python_code):
    """Generate messages for creating main function specification only"""
    main_functions = identify_main_functions(python_code)
    
    if not main_functions:
        # Fallback to original approach if no main_ functions found
        return [
            {
                "role": "system",
                "content": "You are an expert AI assistant that writes Dafny method specifications. You excel at analyzing Python code and creating precise method signatures with preconditions and postconditions for the main function.",
            },
            {
                "role": "user",
                "content": "Here is some Python code:\n\n"
                + python_code
                + "\n\nPlease analyze this Python code and create ONLY the main function specification in Dafny. Focus on:\n\n1. **Main Method Signature**: Create a method signature for the main function with appropriate parameter and return types.\n\n2. **Preconditions**: State any `requires` clauses for the main method (e.g., input validation, domain restrictions, etc.).\n\n3. **Postconditions**: State the logical guarantees about the returned values as `ensures` clauses.\n\n4. **Method Body**: Include only a method body with `ensures false;` to indicate this is just a specification.\n\nDo NOT implement any helper functions or the actual logic. Return only the main function specification as a Dafny snippet that can be parsed by Dafny.",
            },
        ]
    
    # Focus on the first main_ function found
    main_func = main_functions[0]
    
    return [
        {
            "role": "system",
            "content": "You are an expert AI assistant that writes Dafny method specifications. You excel at analyzing Python code and creating precise method signatures with preconditions and postconditions for main functions.",
        },
        {
            "role": "user",
            "content": f"Here is some Python code:\n\n"
            + python_code
            + f"\n\nI found a main function: `{main_func['full_line']}`\n\n"
            + f"Please analyze this Python code and create ONLY the specification for the `{main_func['name']}` function in Dafny. Focus on:\n\n"
            + f"1. **Method Signature**: Create a method signature for `{main_func['name']}` with appropriate parameter and return types based on the Python signature.\n\n"
            + f"2. **Preconditions**: State any `requires` clauses for the method (e.g., input validation, domain restrictions, etc.).\n\n"
            + f"3. **Postconditions**: State the logical guarantees about the returned values as `ensures` clauses.\n\n"
            + f"4. **Method Body**: Include only a method body with `ensures false;` to indicate this is just a specification.\n\n"
            + f"Do NOT implement any helper functions or the actual logic. Return only the `{main_func['name']}` function specification as a Dafny snippet that can be parsed by Dafny.",
        },
    ]


def init_generate_complete_impl_messages(python_code, main_spec):
    """Generate messages for creating complete implementation with main spec as reference"""
    main_functions = identify_main_functions(python_code)
    
    if not main_functions:
        # Fallback to original approach
        return [
            {
                "role": "system",
                "content": "You are an expert AI assistant that writes complete Dafny programs. You excel at writing code with formally verified correctness, providing precise preconditions and postconditions, and finding the appropriate loop invariants to ensure all verification conditions are met.",
            },
            {
                "role": "user",
                "content": "Here is some Python code:\n\n"
                + python_code
                + "\n\nAnd here is the main function specification that was previously generated:\n\n```dafny\n"
                + main_spec
                + "\n```\n\nPlease translate this Python code into a complete Dafny program, ensuring:\n\n1. **Keep the Main Method**: Use the provided main function specification as-is, but implement the actual method body.\n\n2. **Helper Methods**: Create all necessary helper methods with well-defined signatures.\n\n3. **Preconditions**: Clearly state any `requires` clauses for each method (e.g., array length constraints, non-null references, numeric domain restrictions, etc.).\n\n4. **Postconditions**: State the logical guarantees about the returned values or final state as `ensures` clauses (e.g., correctness of returned results, absence of side effects, etc.).\n\n5. **Verification Details**: Include all necessary loop invariants (or other verification hints) so Dafny can prove the postconditions.\n\nReturn the final Dafny code as a self-contained snippet that can be verified by Dafny as-is.",
            },
        ]
    
    # Focus on the main function
    main_func = main_functions[0]
    
    return [
        {
            "role": "system",
            "content": "You are an expert AI assistant that writes complete Dafny programs. You excel at writing code with formally verified correctness, providing precise preconditions and postconditions, and finding the appropriate loop invariants to ensure all verification conditions are met.",
        },
        {
            "role": "user",
            "content": f"Here is some Python code:\n\n"
            + python_code
            + f"\n\nI found a main function: `{main_func['full_line']}`\n\n"
            + f"And here is the specification for `{main_func['name']}` that was previously generated:\n\n```dafny\n"
            + main_spec
            + f"\n```\n\nPlease translate this Python code into a complete Dafny program, ensuring:\n\n"
            + f"1. **Keep the Main Method**: Use the provided `{main_func['name']}` specification as-is, but implement the actual method body.\n\n"
            + f"2. **Helper Methods**: Create all necessary helper methods (like `numSquares_279`, `getMoneyAmount_375`, etc.) with well-defined signatures.\n\n"
            + f"3. **Preconditions**: Clearly state any `requires` clauses for each method (e.g., array length constraints, non-null references, numeric domain restrictions, etc.).\n\n"
            + f"4. **Postconditions**: State the logical guarantees about the returned values or final state as `ensures` clauses (e.g., correctness of returned results, absence of side effects, etc.).\n\n"
            + f"5. **Verification Details**: Include all necessary loop invariants (or other verification hints) so Dafny can prove the postconditions.\n\n"
            + f"Return the final Dafny code as a self-contained snippet that can be verified by Dafny as-is.",
        },
    ]


def debug_main_spec_messages(main_spec, python_code, dafny_analysis_result):
    """Debug messages for main function specification"""
    main_functions = identify_main_functions(python_code)
    
    if not main_functions:
        # Fallback to original approach
        return [
            {
                "role": "system",
                "content": "You are an expert AI assistant that writes and debugs Dafny method specifications. You excel at diagnosing and fixing specification errors based on Dafny parser messages.",
            },
            {
                "role": "user",
                "content": "Below is the Python code:\n\n```python\n"
                + python_code
                + "\n```\n\nAnd the main function specification you previously provided:\n\n```dafny\n"
                + main_spec
                + "\n```\n\nI ran `dafny verify ***.dfy` and received this error message:\n\n```\n"
                + dafny_analysis_result
                + "\n```\n\nCan you please fix the main function specification so that it parses successfully? Output the corrected main function specification only, without any other text.",
            },
        ]
    
    # Focus on the main function
    main_func = main_functions[0]
    
    return [
        {
            "role": "system",
            "content": "You are an expert AI assistant that writes and debugs Dafny method specifications. You excel at diagnosing and fixing specification errors based on Dafny parser messages.",
        },
        {
            "role": "user",
            "content": f"Below is the Python code:\n\n```python\n"
            + python_code
            + f"\n```\n\nI found a main function: `{main_func['full_line']}`\n\n"
            + f"And the specification for `{main_func['name']}` you previously provided:\n\n```dafny\n"
            + main_spec
            + f"\n```\n\nI ran `dafny verify ***.dfy` and received this error message:\n\n```\n"
            + dafny_analysis_result
            + f"\n```\n\nCan you please fix the `{main_func['name']}` function specification so that it parses successfully? Output the corrected function specification only, without any other text.",
        },
    ]


def debug_complete_impl_messages(dafny_code, python_code, main_spec, dafny_analysis_result):
    """Debug messages for complete implementation"""
    main_functions = identify_main_functions(python_code)
    
    if not main_functions:
        # Fallback to original approach
        return [
            {
                "role": "system",
                "content": "You are an expert AI assistant that writes and debugs Dafny programs. You excel at diagnosing and fixing verification errors based on Dafny solver messages, while maintaining correct preconditions, postconditions, and loop invariants.",
            },
            {
                "role": "user",
                "content": "Below is the Python code:\n\n```python\n"
                + python_code
                + "\n```\n\nHere is the main function specification:\n\n```dafny\n"
                + main_spec
                + "\n```\n\nAnd the complete Dafny code you previously provided (which I tried to verify):\n\n```dafny\n"
                + dafny_code
                + "\n```\n\nI ran `dafny verify ***.dfy` and received this error message:\n\n```\n"
                + dafny_analysis_result
                + "\n```\n\nCan you please fix the code so that it verifies successfully? Make sure to keep the main function specification intact. Output the final Dafny code only, without any other text.",
            },
        ]
    
    # Focus on the main function
    main_func = main_functions[0]
    
    return [
        {
            "role": "system",
            "content": "You are an expert AI assistant that writes and debugs Dafny programs. You excel at diagnosing and fixing verification errors based on Dafny solver messages, while maintaining correct preconditions, postconditions, and loop invariants.",
        },
        {
            "role": "user",
            "content": f"Below is the Python code:\n\n```python\n"
            + python_code
            + f"\n```\n\nI found a main function: `{main_func['full_line']}`\n\n"
            + f"Here is the specification for `{main_func['name']}`:\n\n```dafny\n"
            + main_spec
            + f"\n```\n\nAnd the complete Dafny code you previously provided (which I tried to verify):\n\n```dafny\n"
            + dafny_code
            + f"\n```\n\nI ran `dafny verify ***.dfy` and received this error message:\n\n```\n"
            + dafny_analysis_result
            + f"\n```\n\nCan you please fix the code so that it verifies successfully? Make sure to keep the `{main_func['name']}` function specification intact. Output the final Dafny code only, without any other text.",
        },
    ]


def extract_dafny_code(response):
    return response.split("```dafny")[1].split("```")[0]


def verify_dafny_code(result_save_dir, dafny_bin_path, dafny_code, iteration=None):
    if iteration is None:
        iteration = "initial"
    dafny_code_path = f"{result_save_dir}/dafny_code_{iteration}.dfy"
    open(dafny_code_path, "w").write(dafny_code)

    dafny_analysis_path = (
        f"{result_save_dir}/dafny_code_{iteration}.dfy.analysis"
    )

    cmd = f"{dafny_bin_path} verify {dafny_code_path} --verbose >> {dafny_analysis_path}"

    os.system(cmd)

    return open(dafny_analysis_path, "r").read()


def convert_python_to_dafny_multistep(api_manager, python_code, dafny_bin_path, result_save_dir, refine_times=10, process_log_path=None, model_name=None):
    """Multi-step conversion: first generate main spec, then complete implementation"""
    if not os.path.exists(result_save_dir):
        os.makedirs(result_save_dir)
    open(result_save_dir + "/input_python_code.py", "w").write(python_code)

    # Step 1: Generate main function specification
    if process_log_path is not None:
        open(process_log_path, "w").write("Starting multi-step conversion\n")
    
    response = api_manager.call_llm(
        init_generate_main_spec_messages(python_code), model=model_name)
    open(result_save_dir + "/main_spec_response.txt", "w").write(response)
    main_spec = extract_dafny_code(response)
    
    # Verify main specification
    dafny_analysis_result = verify_main_spec(
        result_save_dir, dafny_bin_path, main_spec)

    if process_log_path is not None:
        open(process_log_path, "a").write("main function specification generated\n")

    # Refine main specification if needed
    if ", 0 errors" not in dafny_analysis_result:
        for i in range(refine_times):
            response = api_manager.call_llm(
                debug_main_spec_messages(main_spec, python_code, dafny_analysis_result),
                model=model_name
            )
            open(result_save_dir + f"/main_spec_refine_{i}_response.txt", "w").write(response)
            main_spec = extract_dafny_code(response)
            dafny_analysis_result = verify_main_spec(
                result_save_dir, dafny_bin_path, main_spec, iteration=f"refine_{i}")

            if process_log_path is not None:
                open(process_log_path, "a").write(f"main spec iteration {i} done\n")

            if ", 0 errors" in dafny_analysis_result:
                break

    # Step 2: Generate complete implementation
    if process_log_path is not None:
        open(process_log_path, "a").write("generating complete implementation\n")
    
    response = api_manager.call_llm(
        init_generate_complete_impl_messages(python_code, main_spec), model=model_name)
    open(result_save_dir + "/complete_impl_response.txt", "w").write(response)
    dafny_code = extract_dafny_code(response)
    dafny_analysis_result = verify_dafny_code(
        result_save_dir, dafny_bin_path, dafny_code, iteration="complete")

    if process_log_path is not None:
        open(process_log_path, "a").write("complete Dafny code generated\n")

    if ", 0 errors" in dafny_analysis_result:
        verify_dafny_code(result_save_dir, dafny_bin_path,
                          dafny_code, iteration="final")
        return

    # Refine complete implementation if needed
    for i in range(refine_times):
        response = api_manager.call_llm(
            debug_complete_impl_messages(dafny_code, python_code, main_spec, dafny_analysis_result),
            model=model_name
        )
        open(result_save_dir + f"/complete_refine_{i}_response.txt", "w").write(response)
        dafny_code = extract_dafny_code(response)
        dafny_analysis_result = verify_dafny_code(
            result_save_dir, dafny_bin_path, dafny_code, iteration=f"complete_refine_{i}")

        if process_log_path is not None:
            open(process_log_path, "a").write(f"complete impl iteration {i} done\n")

        if ", 0 errors" in dafny_analysis_result:
            break


def convert_python_to_dafny(api_manager, python_code, dafny_bin_path, result_save_dir, refine_times=10, process_log_path=None, model_name=None, use_multistep=True):
    """Convert Python to Dafny with option for multi-step or single-step approach"""
    if use_multistep:
        return convert_python_to_dafny_multistep(api_manager, python_code, dafny_bin_path, result_save_dir, refine_times, process_log_path, model_name)
    else:
        # Original single-step approach
        if not os.path.exists(result_save_dir):
            os.makedirs(result_save_dir)
        open(result_save_dir + "/input_python_code.py", "w").write(python_code)

        response = api_manager.call_llm(
            init_generate_messages(python_code), model=model_name)
        open(result_save_dir + "/initial_response.txt", "w").write(response)
        dafny_code = extract_dafny_code(response)
        dafny_analysis_result = verify_dafny_code(
            result_save_dir, dafny_bin_path, dafny_code)

        if process_log_path is not None:
            open(process_log_path, "w").write("initial dafny code generated\n")

        if ", 0 errors" in dafny_analysis_result:
            verify_dafny_code(result_save_dir, dafny_bin_path,
                              dafny_code, iteration="0")
            return

        for i in range(refine_times):
            response = api_manager.call_llm(
                debug_messages(dafny_code, python_code, dafny_analysis_result),
                model=model_name
            )
            open(result_save_dir + f"/refine_{i}_response.txt", "w").write(response)
            dafny_code = extract_dafny_code(response)
            dafny_analysis_result = verify_dafny_code(
                result_save_dir, dafny_bin_path, dafny_code, iteration=i)

            if process_log_path is not None:
                open(process_log_path, "a").write(f"iteration {i} done\n")

            if ", 0 errors" in dafny_analysis_result:
                break

def check_translate_success(translate_result_dir, prefix="dafny_code", python_code_prefix="input_python_code"):
    python_code_path = f"{translate_result_dir}/{python_code_prefix}.py"
    if not os.path.exists(python_code_path):
        # print(f"python code path not found: {python_code_path}")
        return False, None, None
    python_code = open(python_code_path, "r").read()

    for i in range(10):
        analysis_i = 9 - i
        analysis_path = os.path.join(
            translate_result_dir, f'{prefix}_{analysis_i}.dfy.analysis')
        if os.path.exists(analysis_path) and os.path.exists(analysis_path):
            dafny_analysis_result = open(
                analysis_path, "r").read()
            # Add "time out" to filter conditions
            if ", 0 errors" in dafny_analysis_result and "time out" not in dafny_analysis_result:
                dafny_code_path = os.path.join(
                    translate_result_dir, f'{prefix}_{analysis_i}.dfy')
                dafny_code = open(dafny_code_path, "r").read()
                return True, python_code, dafny_code
    return False, python_code, None

def check_dafny_analysis_exist(translate_result_dir):
    analysis_path = os.path.join(
        translate_result_dir, f'dafny_code_9.dfy.analysis')
    if os.path.exists(analysis_path):
        return True
    return check_translate_success(translate_result_dir)[0]

def check_translate_result(translate_result_dir):
    if os.path.exists(translate_result_dir):
        if check_dafny_analysis_exist(translate_result_dir):
            return True
    return False

class APIManager:
    def __init__(self):
        key = "your api key"
        self.client = OpenAI(
            base_url="your api platform", api_key=key)

    def call_llm(self, messages, model):
        response = self.client.chat.completions.create(
            model=model,
            messages=messages,
            temperature=0.7,
            top_p=0.8
        )
        return response.choices[0].message.content
