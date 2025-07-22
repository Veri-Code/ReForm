from radon.complexity import cc_visit
from radon.metrics import h_visit
import matplotlib.pyplot as plt
from collections import Counter, defaultdict
from utils import *

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def analyze_code_complexity(code: str) -> list:
    """
    Analyze the complexity of the code.
    """
    return cc_visit(code)

def analyze_halstead_metrics(code: str) -> list:
    """
    Analyze the Halstead metrics of the code.
    """
    return h_visit(code)

def get_max_cc_and_level(code: str) -> tuple[int, str]:
    """
    Get the max cyclomatic complexity and its level for a code string.
    Returns:
        (max_cc, level)
    """
    results = analyze_code_complexity(code)
    if not results:
        return 0, "Simple"
    max_cc = max(r.complexity for r in results)
    if max_cc <= 5:
        level = "Simple"
    elif max_cc <= 10:
        level = "Medium"
    else:
        level = "Complex"
    return max_cc, level

data = jsonl_parser('../../raw_code/LeetCodeDataset-all.jsonl')
codes = [i['completion'] for i in data]

levels = []
cc_values = defaultdict(list)
halstead_values = defaultdict(list)
level_data = defaultdict(list)
for i, code in enumerate(tqdm(codes, desc="Analyzing CC and Halstead")):
    max_cc, level = get_max_cc_and_level(code)
    levels.append(level)
    cc_values[level].append(max_cc)
    data[i]["cc_complex"] = max_cc
    level_data[level].append(data[i])

level_counts = Counter(levels)

for level in ["Simple", "Medium", "Complex"]:
    jsonl_dumper(level_data[level], f"../../raw_code/{level.lower()}_leetcodes.jsonl")

plt.figure(figsize=(10, 6))
for level in ["Simple", "Medium", "Complex"]:
    plt.hist(cc_values[level], bins=20, alpha=0.5, label=level)
plt.xlabel("Cyclomatic Complexity")
plt.ylabel("Number of Codes")
plt.title("CC Distribution by Level")
plt.legend()
plt.savefig("../../plots/cc_distribution_by_level.png")
plt.show()
