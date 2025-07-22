import os
import sys
import argparse
import glob
from tqdm import tqdm
import multiprocessing as mp
from python2dafny_utils import (
    APIManager, 
    convert_python_to_dafny,
    identify_main_functions
)
import random
import shutil
random.seed(42)

def parse_args():
    parser = argparse.ArgumentParser(description='Convert Python files in to Dafny')
    parser.add_argument('--input-dir', type=str, 
                       required=True,
                       help='Input directory containing Python files')
    parser.add_argument('--output-dir', type=str,
                       required=True,
                       help='Output directory for Dafny results')
    parser.add_argument('--dafny-bin', type=str,
                       required=True,
                       help='Path to Dafny binary')
    parser.add_argument('--refine-times', type=int, default=10,
                       help='Number of refinement iterations')
    parser.add_argument('--model', type=str, default="claude-sonnet-4-20250514",
                       help='Model name to use')
    parser.add_argument('--use-multistep', action='store_true', default=True,
                       help='Use multi-step conversion')
    parser.add_argument('--use-single-step', action='store_true', default=False,
                       help='Use single-step conversion')
    return parser.parse_args()

def find_python_files(directory):
    """Find all Python files in the directory"""
    python_files = []
    for item in os.listdir(directory):
        item_path = os.path.join(directory, item)
        if os.path.isdir(item_path):
            # Look for .py file with same name as directory
            py_file = os.path.join(item_path, f"{item}.py")
            if os.path.exists(py_file):
                python_files.append((item, py_file))
    return python_files

def coverting_file(python_files, args):
    api_manager = APIManager()
    successful_conversions = 0
    failed_conversions = 0
    
    for file_name, file_path in tqdm(python_files, desc="Converting files"):
        print(f"\nProcessing: {file_name}")
        
        # if the folder is already processed, skip it
        if os.path.exists(os.path.join(args.output_dir, file_name)):
            print(f"  Skipping {file_name} as it is already processed.")
            successful_conversions += 1
            continue
        
        try:
            # Read Python file
            with open(file_path, 'r', encoding='utf-8') as f:
                python_code = f.read()
            
            # Check if main functions exist
            main_functions = identify_main_functions(python_code)
            if not main_functions:
                print(f"  Warning: No main functions found in {file_name}")
                failed_conversions += 1
                continue
            
            print(f"  Found main function: {main_functions[0]['name']}")
            
            # Create output directory for this file
            file_output_dir = os.path.join(args.output_dir, file_name)
            if not os.path.exists(file_output_dir):
                os.makedirs(file_output_dir)
            
            # Convert using multi-step approach
            convert_python_to_dafny(
                api_manager=api_manager,
                python_code=python_code,
                dafny_bin_path=args.dafny_bin,
                result_save_dir=file_output_dir,
                refine_times=args.refine_times,
                process_log_path=os.path.join(file_output_dir, "process.log"),
                model_name=args.model,
                use_multistep=args.use_multistep
            )
            
            # Check if there is verified Dafny code, and save as dafny_code_final.dfy
            from python2dafny_ori import check_translate_success
            success, _, dafny_code = check_translate_success(file_output_dir)
            if success and dafny_code is not None:
                final_path = os.path.join(file_output_dir, "dafny_code_final.dfy")
                with open(final_path, "w") as f:
                    f.write(dafny_code)
                print(f"  ✓ Verified Dafny code saved as dafny_code_final.dfy in {file_output_dir}")
            else:
                # If not verified, remove the folder
                print(f"  ✗ No verified Dafny code, removing folder: {file_output_dir}")
                shutil.rmtree(file_output_dir)
                failed_conversions += 1
                continue
            
            successful_conversions += 1
            print(f"  ✓ Successfully converted {file_name}")
            
        except Exception as e:
            failed_conversions += 1
            print(f"  ✗ Error converting {file_name}: {e}")
    

def convert_files(args):
    """Convert all Python files to Dafny, then keep only 50 successful conversions with dafny_code_final.dfy"""
    print(f"Input directory: {args.input_dir}")
    print(f"Output directory: {args.output_dir}")
    print(f"Dafny binary: {args.dafny_bin}")
    print(f"Refine times: {args.refine_times}")
    print(f"Model: {args.model}")
    print(f"Multi-step: {args.use_multistep}")
    print("-" * 60)
    
    # Check if input directory exists
    if not os.path.exists(args.input_dir):
        print(f"Error: Input directory {args.input_dir} does not exist!")
        return
    
    # Create output directory
    if not os.path.exists(args.output_dir):
        os.makedirs(args.output_dir)
        print(f"Created output directory: {args.output_dir}")
    
    # Initialize API manager
    print("Initializing API manager...")
    
    # Find all Python files
    print(f"Scanning directory: {args.input_dir}")
    python_files = find_python_files(args.input_dir)
    
    if not python_files:
        print("No Python files found!")
        return
    
    print(f"Found {len(python_files)} Python files to convert")
    
    # Batch processing with multiprocessing
    num_processes = min(20, len(python_files))
    batches = []
    batch_size = (len(python_files) + num_processes - 1) // num_processes
    for i in range(0, len(python_files), batch_size):
        batch = python_files[i:i+batch_size]
        batches.append((batch, args))
    with mp.Pool(processes=num_processes) as pool:
        pool.starmap(coverting_file, batches)
    
    # Post-processing: filter and organize
    print("\nPost-processing: filtering only successful Dafny code folders...")
    from python2dafny_ori import check_translate_success
    success_folders = []
    for file_name in os.listdir(args.output_dir):
        file_output_dir = os.path.join(args.output_dir, file_name)
        if os.path.isdir(file_output_dir):
            success, _, dafny_code = check_translate_success(file_output_dir)
            if success and dafny_code is not None:
                final_path = os.path.join(file_output_dir, "dafny_code_final.dfy")
                with open(final_path, "w") as f:
                    f.write(dafny_code)
                success_folders.append(file_output_dir)
            else:
                shutil.rmtree(file_output_dir)
    # Only keep copies of the first 50 successful folders in a new directory
    selected_dir = args.output_dir + "_selected_50"
    if not os.path.exists(selected_dir):
        os.makedirs(selected_dir)
    if len(success_folders) > 50:
        selected_folders = random.sample(success_folders, 50)
    else:
        selected_folders = success_folders
    for folder in selected_folders:
        base_name = os.path.basename(folder)
        dst = os.path.join(selected_dir, base_name)
        if not os.path.exists(dst):
            shutil.copytree(folder, dst)
    print(f"Randomly selected {len(selected_folders)} successful folders copied to {selected_dir}")
    print(f"Post-processing finished. {len(success_folders)} successful Dafny code folders saved.")

def main():
    args = parse_args()
    
    # Determine conversion approach
    if args.use_single_step:
        args.use_multistep = False
    
    print("Python to Dafny Conversion for random_50 directory")
    print("=" * 60)
    
    convert_files(args)

if __name__ == "__main__":
    main() 