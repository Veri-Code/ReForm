import difflib

def is_fuzzy_match(original, modified):
    """
    验证 modified 是否是 original 插入若干行以及增加或减少空白字符后得到的。
    
    :param original: 原始字符串
    :param modified: 修改后的字符串
    :return: 如果 modified 是 original 的模糊匹配结果，则返回 True，否则返回 False
    """
    # 将字符串按行分割
    original_lines = original.splitlines()
    modified_lines = modified.splitlines()
    
    # 使用 difflib.Differ 比较字符串
    differ = difflib.Differ()
    diff = list(differ.compare(original_lines, modified_lines))
    
    # 检查差异
    for line in diff:
        if line.startswith('? '):  # 忽略空白字符的差异
            continue
        if line.startswith('- '):  # 原始字符串中有但修改后的字符串中没有的行
            return False
        if line.startswith('+ '):  # 修改后的字符串中有但原始字符串中没有的行
            continue  # 允许插入行
        if line.startswith('  '):  # 完全相同的行
            continue
    
    return True

# 示例
import pandas as pd
import random
file = pd.read_parquet("/nas/shared/sys2/liyizhi/TinyZero_Dafny_0403/dataset5k_not_trained/test.parquet")
for idx in random.sample(range(len(file)), 100):
    original = file["input"][idx]

    modified = file["output"][idx]
    if not is_fuzzy_match(original, modified):
        print(original)
        print(modified)
        print("\n")
    # print(is_fuzzy_match(original, modified))