import re
import os
import matplotlib.pyplot as plt
folder_name = "/nas/shared/sys2/liyizhi/full_log/DLC_4nodes_7B_0502_Bo16"

all_data = []

# lengths = []
rollout = 1
total_index = 40
for index in range(500):
# for index in range(100000, 104500):
    try:
        filelists = os.listdir(os.path.join(folder_name, str(index)))
        filelists = [int(x[:-4]) for x in filelists if x.endswith(".dfy")]

        filelists = sorted(filelists)
        values = []
        for j in range(len(filelists)):
            temp = -3
            string = os.path.join(folder_name, str(index), f"out-{filelists[j]}.txt")
            data = open(string, "r").read()
            pattern = re.compile(r"Dafny program verifier finished with (\d+) verified, (\d+) error")
            match = pattern.search(data)
            if match:
                temp = int(match.group(2))
            else:
                if "resolution/type error" in data:
                    temp = -1
                elif "parse error" in data:
                    temp = -2
            
            values.append(temp)
        
    except:
        pass

    all_data.append(values)
        # missing_index_num += 1


# print(initial_counts)
# print(final_counts)
# print(missing_index_num)

# print(all_data)

def pick_from(input_list):
    # if all negative, take the maximum one
    if all(x < 0 for x in input_list):
        return max(input_list)
    else:
        # return the smallest positive one
        return min([x for x in input_list if x >= 0])

for concerned_num in [-2, -1, 0, 1, 2]:
    ratios = []
    for i in range(1, total_index):
        total = 0
        concerned = 0
        for j in all_data:
            if len(j) < i * rollout:
                continue
            total += 1
            if pick_from(j[i*rollout-1:(i+1)*rollout-1]) == concerned_num:
                concerned += 1
            
        if total == 0:
            ratio = 0
        else:
            ratio = concerned/total
        ratios.append(ratio)
    plt.plot(range(1, total_index), ratios, label=f"{concerned_num}")

plt.legend()
name = folder_name.split("/")[-1]
plt.savefig(f"{name}.png")


