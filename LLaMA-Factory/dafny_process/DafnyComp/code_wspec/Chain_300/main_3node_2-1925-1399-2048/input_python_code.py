from collections import Counter
from itertools import count
from math import sqrt
from typing import Counter


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
    # output: 0 <= <output> <= 1000000
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


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: unconstrained
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = countTriples_1925(o)
    o2: object = countLargestGroup_1399(o1)
    o3: object = nextBeautifulNumber_2048(o2)
    return o3
