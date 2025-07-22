from collections import Counter
from math import sqrt
from typing import Counter


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 100000000
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


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 1 <= <output> <= 2147483648
    (a, b) = (str(num), str(num))
    for c in a:
        if c != "9":
            a = a.replace(c, "9")
            break
    if b[0] != "1":
        b = b.replace(b[0], "1")
    else:
        for c in b[1:]:
            if c not in "01":
                b = b.replace(c, "0")
                break
    return int(a) - int(b)


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 250
    ans = 0
    while n != 1:
        if n & 1 == 0:
            n >>= 1
        elif n != 3 and n & 3 == 3:
            n += 1
        else:
            n -= 1
        ans += 1
    return ans


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: unconstrained
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = countLargestGroup_1399(o)
    o2: object = maxDiff_1432(o1)
    o3: object = integerReplacement_397(o2)
    o4: object = countTriples_1925(o3)
    return o4
