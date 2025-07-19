from verl.inference.model_utils.SampleItems import SampleItem, SampleItemList, DafnyResponse, OutputItem, MULTIPLICATION_CONSTANT
from verl.inference.model_utils.models import QwenModel
from tqdm import tqdm
import pandas as pd
import os  
from verl.utils.fs import copy_to_local
import torch
import ast
import numpy as np
import json

class DafnyPromptTemplates:
    """Class containing all Dafny prompt templates."""

    @staticmethod
    def cot_wexample(input_problem, previous_output=None):
        example = DafnyPromptTemplates.get_example()
        return f"""<|im_start|>system
You are an expert in dafny. You first thinks about the reasoning process in the mind and then provides the user with the answer.<|im_end|>
<|im_start|>user
Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Here is an example of invariant: <example>{example}</example>. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines.
Show your work in <think> </think> tags. And return the final answer in <answer>```dafny </answer> tags, DO NOT output you answer in <think></think>: return you answer in <ansewr></answer> tags. For example: <answer>```dafny method some_method ... ```</answer>.  Below is the program: ```dafny

{input_problem}
<|im_end|>
<|im_start|>assistant
Let me solve this step by step.
<think> Well, """

    @staticmethod
    def sft(input_problem, previous_output=None):
        prefix = f"<|im_start|>system\nYou are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed.\n<|im_end|>\n<|im_start|>user\nGiven a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n\n{input_problem}```<|im_end|>\n<|im_start|>assistant\n"
        return prefix

    @staticmethod
    def formal_cot(input_problem, previous_output=None):
        """Formal chain-of-thought prompt template."""
        prefix = f"<|im_start|>system\n<|im_end|>\n<|im_start|>user\nYou are given a Dafny program with functions and implementations, but no specification clauses. Only in <think>…</think>, reason in valid Dafny code with intermediate specification constructs (e.g. loop invariants, decreases clauses, assert statements, ghost code, helper lemmas, modifies clauses). Only in <answer>...</answer>, output the complete Dafny module, preserving all function signatures and lemma declarations exactly. Add the weakest requires and strongest ensures that allow the verifier to succeed, and fully characterize the code’s behavior, along with other necessary intermediate specifications from your `<think>` section. If you need to revise your reasoning, rewrite necessary functions in the think process as new ones whose names embed the original so think section gives no parse error, rather than patching individual lines. Do not ever modify the given lines. Never introduce any assume clauses. Output nothing outside the tags. Below is the program:\n```dafny\n\n{input_problem}```<|im_end|>\n<|im_start|>assistant\n"

        return prefix
        
    @staticmethod
    def cot_multi(input_problem, previous_output=None):
        input_problem = input_problem.replace("```dafny", "").replace("```", "")
        return f"""<|im_start|>system
You are a fommal verification expert specializing in Dafny. You will be given programing problems, and your job is to write a correct and fully annotated Dafny program.

You must only output the following structured blocks:
1. <Dafny> ...</Dafny> : Contains only valid Dafny code.
2. <Answer> ... </Answer> : Used **only when** you have written a complete, verified solution.
3. Never output anything outside of those tags.
4. If the program does not yet verify, wait for compiler feedback between turns.

The input may also include:
- <compiler> ...</compiler> blocks: These contain compiler messages to help you debug.
You may use them to revise your Dafny code in future <Dafny> blocks.

Once you are confident the program is complete and has passed verification, output an <Answer> block with a brief summary of your solution.

Always end your response at </Dafny> or </Answer>.
<|im_end|>
<|im_start|>user
Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:
<Dafny>
{input_problem}
</Dafny>
<|im_end|>
<|im_start|>assistant
<Dafny>
"""

class LLMInference:
    """Class for handling LLM inference and prompt modification operations."""
    
    def __init__(self, model, batch_size=32, prompt_type="sft"):
        self.model = model
        self.batch_size = batch_size
        self.prompt_type = prompt_type
        self.prompt_func = getattr(DafnyPromptTemplates, prompt_type)
    
    def modify_prompts(self, input_item_list, prompt_type=None):
        """Modify prompts based on the specified type."""
        if prompt_type:
            self.prompt_type = prompt_type
            self.prompt_func = getattr(DafnyPromptTemplates, prompt_type)
            
        for item in input_item_list:
            item.llm_input = self.prompt_func(item.org_input, item.output)
        return input_item_list
    
    def modify_parquet_file(self, input_file: str, output_file: str = None, output_dir: str = None):
        """
        Load parquet file, modify prompts, and save to new file.
        Returns the path to the modified file.
        
        Args:
            input_file: Path to input parquet file
            output_file: Optional path to save modified parquet file. If None, will generate one.
            output_dir: Optional directory to save output file. If provided, overrides the directory in output_file.
        """
        print(f"Loading parquet file from {input_file}")
        
        # Generate output file path if not provided
        if output_file is None:
            basename = os.path.basename(input_file)
            if output_dir:
                output_file = os.path.join(output_dir, f"{self.prompt_type}_{basename}")
            else:
                dirname = os.path.dirname(input_file)
                output_file = os.path.join(dirname, f"{self.prompt_type}_{basename}")
        elif output_dir:
            # If both output_file and output_dir are provided, use output_dir as the directory
            output_file = os.path.join(output_dir, os.path.basename(output_file))

        if os.path.exists(output_file):
            print(f"Output file {output_file} already exists. Skipping modification.")
            return output_file
        
        # Copy to local if needed
        local_input = copy_to_local(input_file)
        
        # Load and modify the parquet file
        df = pd.read_parquet(local_input)
        print("Modifying prompts...")
        modified_df = pd.DataFrame([self._modify_row(row) for _, row in tqdm(df.iterrows())])
        modified_df = modified_df.loc[:20]
        
        # Save modified file
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        print(f"Saving modified parquet file to {output_file}")
        
        # Convert JSON strings back to objects before saving
        if 'prompt' in modified_df.columns:
            try:
                modified_df['prompt'] = modified_df['prompt'].apply(lambda x: json.loads(x) if isinstance(x, str) and x.startswith('[') else x)
            except:
                pass  # Keep as is if JSON parsing fails
                
        modified_df.to_parquet(output_file, index=False)
        print("Done!")
        
        return output_file
    
    def _modify_row(self, row):
        """Modify a single row's prompt."""
        import ast
        import numpy as np
        import json
        
        # Try to parse the prompt based on its type
        input_content = row['input']
        prompt = row['prompt']
        
        # Handle numpy array
        if isinstance(prompt, np.ndarray):
            # Convert numpy array to list if it contains objects
            prompt = prompt.tolist()
            
        # Apply the prompt transformation
        modified_prompt = self.prompt_func(input_content)
        
        # Update the prompt format to match expected structure
        if isinstance(prompt, list):
            prompt[0]['content'] = modified_prompt
            # Convert to JSON string for parquet compatibility
            row['prompt'] = json.dumps(prompt)
        else:
            row['prompt'] = modified_prompt
        return row
    
    def run_inference(self, input_item_list: SampleItemList, shot_number: int = 1, generation_config=None):
        """
        Run inference on the input items.
        
        Args:
            input_item_list: List of input items to process
            shot_number: Number of shots for inference
            generation_config: Generation configuration (e.g. config.rollout)
        
        Returns:
            List of lists, where each inner list contains shot_number outputs for each input
            Format: [[input1_shot1, input1_shot2, ...], [input2_shot1, input2_shot2, ...], ...]
        """
        input_item_list = self.modify_prompts(input_item_list)
        inputs = [item.llm_input for item in input_item_list]
        
        # Run model inference with generation config and multishot
        # Returns: [[input1_shot1, input1_shot2, ...], [input2_shot1, input2_shot2, ...], ...]
        outputs = self.model.obtain_multiple_answer_multishot(inputs, 
                                                            generation_config, 
                                                            shot_number)
        
        return inputs,outputs
    
    def process_parquet_and_run(self, input_file: str, output_file: str = None, output_dir: str = None, generation_config=None, shot_number: int = 1, prompt_type: str = None):
        """
        Convenience method to modify prompts in a parquet file and run inference in one go.
        
        Args:
            input_file: Path to input parquet file
            output_file: Optional path to save modified parquet file
            output_dir: Optional directory to save output file
            generation_config: Generation configuration (e.g. config.rollout)
            shot_number: Number of shots for inference
            prompt_type: Type of prompt to use (e.g. 'sft', 'cot_wexample', etc.)
            
        Returns:
            Tuple of (modified_file_path, outputs) where outputs is the model output tensor
        """
        # Update prompt type if provided
        if prompt_type:
            self.prompt_type = prompt_type
            self.prompt_func = getattr(DafnyPromptTemplates, prompt_type)
            
        # Modify prompts
        modified_file = self.modify_parquet_file(input_file, output_file, output_dir)
        
        # Load modified data into SampleItemList
        df = pd.read_parquet(modified_file)
        input_items = SampleItemList()
        for _, row in df.iterrows():
            item = SampleItem(
                org_input=row['input'],
                llm_input=row['prompt'],  # Will be modified by modify_prompts
                org_input_id=row.get('index', -1)
            )
            input_items.append(item)
        
        # Modify prompts in memory and run inference
        # input_items = self.modify_prompts(input_items)
        outputs = self.run_inference(input_items, shot_number, generation_config)
        
        return modified_file, outputs


