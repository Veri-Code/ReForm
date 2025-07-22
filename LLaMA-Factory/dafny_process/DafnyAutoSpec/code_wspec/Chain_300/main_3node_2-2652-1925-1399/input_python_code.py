from collections import Counter
from math import sqrt
from typing import Counter


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 1 <= <output> <= 250
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 10000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: unconstrained
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = sumOfMultiples_2652(o)
    o2: object = countTriples_1925(o1)
    o3: object = countLargestGroup_1399(o2)
    return o3
