from collections import Counter
from math import sqrt
from typing import Counter


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 2 <= <output> <= 100000
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


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 10000
    while 1:
        (t, s, i) = (n, 0, 2)
        while i <= n // i:
            while n % i == 0:
                n //= i
                s += i
            i += 1
        if n > 1:
            s += n
        if s == t:
            return t
        n = s


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 250
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
    o1: object = integerReplacement_397(o)
    o2: object = smallestValue_2507(o1)
    o3: object = countLargestGroup_1399(o2)
    o4: object = countTriples_1925(o3)
    return o4
