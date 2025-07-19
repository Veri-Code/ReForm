import json
import os
from verl.utils.reward_score.condition_comparison_fixed import *
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading
from tqdm import tqdm

eval_result_dir = "/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/sft_ckpt/saves"
eval_result_file = os.path.join(eval_result_dir, "eval_results.json")

eval_result_baseline_dir = "/nas/shared/sys2/chefengdi/eval_log/DLC_naive_128/DLC_4nodes_3B_reward_naive_0513_v5/global_step_60"
eval_result_baseline_file = os.path.join(eval_result_dir, "eval_results.json")

output_folder = "/nas/shared/sys2/liyizhi/folder-0630/sft_all_merge_128"
os.makedirs(output_folder, exist_ok=True)
with open(eval_result_file, 'r', encoding='utf-8') as file:
    json_data = json.load(file)

with open(eval_result_baseline_file, 'r', encoding='utf-8') as file:
    json_data_baseline = json.load(file)

# for i in range(1):
def process_single_index(index, BoN=128):
    
    i = index
    filtered = []
    for j in range(BoN):
        if json_data[str(i)]["shots"][j]["score"][1] == 1:
            filtered.append(j)
    # print(filtered)
    # break

    file_names = os.listdir(f"{eval_result_dir}/{i}")
    numbers = [int(x[:-4]) for x in file_names if x.endswith(".dfy") and x != "gt.dfy"]
    numbers = sorted(numbers)
    # print(len(numbers))
    # print(sorted(numbers))

    # correct_numbers = []
    # for j in filtered:
    #     correct_numbers.append(numbers[j])

    num_files = len(numbers)
    # print(num_files)

    if num_files == 0:
        print(f"No verified files for {i}")
        # Check if baseline generates verifiable codes in the first 8 shots
        # If so, check if any clauses are corrected with minor modifications
        for j in range(8):
            if json_data_baseline[str(i)]["shots"][j]["score"][1] == 1:
                print(f"Baseline verifies {i} in shot {j}")
        with open(f"{output_folder}/{i}.dfy", 'w') as f:
            f.write("No verified files")
        return 0

    datas = []
    print(num_files)
    for t in range(num_files):
        with open(f"{eval_result_dir}/{i}/{numbers[t]}.dfy", "r") as f:
            data = f.read()

        # if t == 0:
        #     org_code = hint_remove(data).split("\n")
        # data = data.split("\n")
        # datas.append(data)
        spec_ensures = extract_specs(data)
        print(spec_ensures["CalculateOrderTotals"]["ensures"])
    
# #     with open("126951.dfy", "r") as f:
# #     data1 = f.read()

# # with open("173793.dfy", "r") as f:
# #     data2 = f.read()

#     # code_body = hint_remove(datas[0])

# # print(code_body)

#     ptrs = [0] * num_files
#     ptr_org = 0

#     lines = []
# # line1 = data1.split("\n")
# # line2 = data2.split("\n")
# # org_code = code_body.split("\n")
#     while True:

#         line_set = set()

#         for t in range(num_files):
#             while ptrs[t] < len(datas[t]) and datas[t][ptrs[t]] != org_code[ptr_org]:
#                 cur_line = datas[t][ptrs[t]].strip()
#                 if cur_line not in line_set:
#                     line_set.add(cur_line)
#                     lines.append(cur_line)
#                 ptrs[t] += 1
#                 # lines.append(datas[t][ptrs[t]])
#                 # line_set.add(datas[t][ptrs[t]].strip())
#                 # ptrs[t] += 1

#         # for line in line_set:
#         #     lines.append(line)


#         lines.append(org_code[ptr_org])
#         ptr_org += 1

#         for t in range(num_files):
#             ptrs[t] += 1

#         if ptr_org >= len(org_code):

#             for t in range(num_files):
#                 while ptrs[t] < len(datas[t]):
#                     lines.append(datas[t][ptrs[t]])
#                     ptrs[t] += 1
#             break

#     with open(f"{output_folder}/{i}.dfy", 'w') as f:
#         f.write("\n".join(lines))
    
#     return 0

# indices = list(range(512))  # You can adjust this range as needed

# processed_count = 0
# skipped_count = 0
# total_scores = []
# max_workers = 48
# BON=128
# with ThreadPoolExecutor(max_workers=max_workers) as executor:
#     # Submit all tasks
#     future_to_index = {executor.submit(process_single_index, index, BON): index 
#                         for index in indices}
    
#     # Process completed tasks with progress bar
#     with tqdm(total=len(indices), desc="Processing indices") as pbar:
#         for future in as_completed(future_to_index):
#             result = future.result()
#             if result is not None:
#                 processed_count += 1
#                 total_scores.append(result)
#             else:
#                 skipped_count += 1
#             pbar.update(1)

process_single_index(9)

# for t in range(10):
#     # os.system(f"cat /nas/shared/sys2/chefengdi/eval_log/3B_sft_128/sft_ckpt/saves/0/out-{numbers[t]}.txt")
#     with open(f"/nas/shared/sys2/chefengdi/eval_log/3B_sft_128/sft_ckpt/saves/0/out-{numbers[t]}.txt", "r") as g:
#         temp = g.readlines()
#         print(temp)
#     print("----------")
# results_dict = {exp_name: {step: {} for step in global_steps + [0]} for exp_name in exp_names}
#     for exp_name in exp_names:
#         for step in global_steps + [0]:
#             for shot in range(1, max_shot + 1):
#                 results_dict[exp_name][step][shot] = []

#     for file_dir in file_dirs:
#         for step in global_steps:
#             exp_name = file_dir.split("/")[-1]
#             import json
#             with open(os.path.join(file_dir, f"global_step_{step}","eval_results.json"), "r") as f:
#                 step_results = json.load(f)
#             for sample_id, sample_data in step_results.items():
#                 if isinstance(sample_id, str) and sample_id.isdigit():
#                     for shot_data in sample_data["shots"]:
#                         shot_num = shot_data["shot_number"]
#                         if shot_num <= max_shot:
#                             results_dict[exp_name][step][shot_num].append(shot_data["score"])