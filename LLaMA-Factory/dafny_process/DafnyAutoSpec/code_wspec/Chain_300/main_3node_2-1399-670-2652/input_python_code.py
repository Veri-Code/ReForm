from collections import Counter
from typing import Counter


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 0 <= <output> <= 100000000
    cnt = Counter()
    ans = mx = 0
    for i in range(1, n + 1):
        s = 0
        while i:
            s += i % 10
            i //= 10
        cnt[s] += 1
        if mx < cnt[s]:
            mx = cnt[s]
            ans = 1
        elif mx == cnt[s]:
            ans += 1
    return ans


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: 1 <= <output> <= 1000
    s = list(str(num))
    n = len(s)
    d = list(range(n))
    for i in range(n - 2, -1, -1):
        if s[i] <= s[d[i + 1]]:
            d[i] = d[i + 1]
    for i, j in enumerate(d):
        if s[i] < s[j]:
            (s[i], s[j]) = (s[j], s[i])
            break
    return int("".join(s))


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: unconstrained
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = countLargestGroup_1399(o)
    o2: object = maximumSwap_670(o1)
    o3: object = sumOfMultiples_2652(o2)
    return o3
