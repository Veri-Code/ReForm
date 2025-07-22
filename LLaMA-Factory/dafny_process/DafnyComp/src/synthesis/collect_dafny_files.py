"""
Script to collect all dafny_code.dfy files from the success_code directory
and store them in a JSON file with the format {"dafny": code_content, "source": dir_name}
"""

import os
import json
import glob
from pathlib import Path

def collect_dafny_files(base_path: str) -> list:
    """
    Recursively collect all dafny_code.dfy files from the given base path
    
    Args:
        base_path: The base directory to search for dafny files
        
    Returns:
        List of dictionaries with format {"dafny": code_content, "source": dir_name}
    """
    dafny_files = []
    
    # Find all dafny_code.dfy files recursively
    pattern = os.path.join(base_path, "**", "dafny_code.dfy")
    dafny_paths = glob.glob(pattern, recursive=True)
    
    print(f"Found {len(dafny_paths)} dafny files")
    
    for dafny_path in dafny_paths:
        try:
            # Get the relative path from base_path to use as source
            rel_path = os.path.relpath(dafny_path, base_path)
            # Remove the filename to get just the directory name
            dir_name = os.path.dirname(rel_path)
            
            # Read the dafny file content
            with open(dafny_path, 'r', encoding='utf-8') as f:
                dafny_content = f.read()
            
            # Store in list with format {"dafny": code_content, "source": dir_name}
            dafny_files.append({
                "dafny": dafny_content,
                "source": dir_name
            })
            
            print(f"Processed: {dir_name}")
            
        except Exception as e:
            print(f"Error reading {dafny_path}: {e}")
    
    return dafny_files

def main():
    """Main function to collect dafny files and save to JSON"""
    # Define the base path where success_code directory is located
    base_path = "../../code_wspec/Chain_300"
    
    # Check if the directory exists
    if not os.path.exists(base_path):
        print(f"Error: Directory {base_path} does not exist")
        return
    
    print(f"Searching for dafny files in: {base_path}")
    
    # Collect all dafny files
    dafny_data = collect_dafny_files(base_path)
    
    # Save to JSON file
    output_file = "../../code_wspec/dfyautospec_chain300.json"
    try:
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(dafny_data, f, indent=2, ensure_ascii=False)
        
        print(f"\nSuccessfully saved {len(dafny_data)} dafny files to {output_file}")
        print(f"Total size: {os.path.getsize(output_file)} bytes")
        
    except Exception as e:
        print(f"Error saving to {output_file}: {e}")

if __name__ == "__main__":
    main() 