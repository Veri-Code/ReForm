from collections import Counter
from typing import Counter


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: 1 <= <output> <= 100000
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


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 10000
    ans = cnt = 0
    while n:
        if n & 1:
            cnt += 1
        elif cnt:
            ans += 1
            cnt = 0 if cnt == 1 else 1
        n >>= 1
    if cnt == 1:
        ans += 1
    elif cnt > 1:
        ans += 2
    return ans


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 2 <= <output> <= 100000
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


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: unconstrained
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = maximumSwap_670(o)
    o2: object = minOperations_2571(o1)
    o3: object = countLargestGroup_1399(o2)
    o4: object = smallestValue_2507(o3)
    return o4
