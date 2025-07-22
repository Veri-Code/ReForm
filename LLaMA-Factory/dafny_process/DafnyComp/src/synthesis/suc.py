import os
from python2dafny_utils import check_translate_success

dafny_gen_dir = "../../code_wspec/Chain_300_python"

success_count = 0
total_count = 0

success_folders = []
failed_folders = []

for folder in os.listdir(dafny_gen_dir):
    if os.path.isdir(os.path.join(dafny_gen_dir, folder)):
        translate_result_dir = os.path.join(dafny_gen_dir, folder)
        success, python_code, dafny_code = check_translate_success(translate_result_dir,
        prefix='dafny_code_complete_refine')
        if success:
            success_folders.append(folder)
            success_count += 1
        else:
            failed_folders.append(folder)
        total_count += 1
        

print(f"success_count: {success_count}, total_count: {total_count}, success_rate: {success_count / total_count}")

success_code_dir = "../../code_wspec/Chain_300"
if not os.path.exists(success_code_dir):
    os.makedirs(success_code_dir)

for folder in success_folders:
    translate_result_dir = os.path.join(dafny_gen_dir, folder)
    python_code_path = os.path.join(translate_result_dir, 'input_python_code.py')
    # find success dafny code
    
    for i in range(10):
        analysis_i = 9 - i
        dafny_code_path = os.path.join(
            translate_result_dir, f'dafny_code_complete_refine_{analysis_i}.dfy')
        if os.path.exists(dafny_code_path):
            break
    else:
        print(f"No dafny code found in {folder}, skipping.")
        continue
    
    if os.path.exists(python_code_path) and os.path.exists(dafny_code_path):
        if not os.path.exists(os.path.join(success_code_dir, folder)):
            os.makedirs(os.path.join(success_code_dir, folder))
        # copy python code and dafny code to success_code_dir
        shutil.copy(python_code_path, os.path.join(success_code_dir, folder, f"input_python_code.py"))
        shutil.copy(dafny_code_path, os.path.join(success_code_dir, folder, f"dafny_code.dfy"))
        # print(f"Copied {folder} to {success_code_dir}")
    else:
        print(f"Missing files in {folder}, skipping.")