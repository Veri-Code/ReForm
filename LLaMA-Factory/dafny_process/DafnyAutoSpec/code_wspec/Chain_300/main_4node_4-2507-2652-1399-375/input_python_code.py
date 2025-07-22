from collections import Counter
from typing import Counter


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 1000
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


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 1 <= <output> <= 10000
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 200
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


def getMoneyAmount_375(n: int) -> int:
    # input: 1 <= n <= 200
    # output: unconstrained
    f = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(n - 1, 0, -1):
        for j in range(i + 1, n + 1):
            f[i][j] = j + f[i][j - 1]
            for k in range(i, j):
                f[i][j] = min(f[i][j], max(f[i][k - 1], f[k + 1][j]) + k)
    return f[1][n]


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = smallestValue_2507(o)
    o2: object = sumOfMultiples_2652(o1)
    o3: object = countLargestGroup_1399(o2)
    o4: object = getMoneyAmount_375(o3)
    return o4
