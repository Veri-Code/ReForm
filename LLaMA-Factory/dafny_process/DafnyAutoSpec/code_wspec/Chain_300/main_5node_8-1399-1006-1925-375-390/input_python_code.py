from collections import Counter
from math import sqrt
from typing import Counter


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 10000
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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 250
    k = 0
    stk = [n]
    for x in range(n - 1, 0, -1):
        if k == 0:
            stk.append(stk.pop() * x)
        elif k == 1:
            stk.append(int(stk.pop() / x))
        elif k == 2:
            stk.append(x)
        else:
            stk.append(-x)
        k = (k + 1) % 4
    return sum(stk)


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 200
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def getMoneyAmount_375(n: int) -> int:
    # input: 1 <= n <= 200
    # output: 1 <= <output> <= 1000000000
    f = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(n - 1, 0, -1):
        for j in range(i + 1, n + 1):
            f[i][j] = j + f[i][j - 1]
            for k in range(i, j):
                f[i][j] = min(f[i][j], max(f[i][k - 1], f[k + 1][j]) + k)
    return f[1][n]


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: unconstrained
    (a1, an) = (1, n)
    (i, step, cnt) = (0, 1, n)
    while cnt > 1:
        if i % 2:
            an -= step
            if cnt % 2:
                a1 += step
        else:
            a1 += step
            if cnt % 2:
                an -= step
        cnt >>= 1
        step <<= 1
        i += 1
    return a1


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = countLargestGroup_1399(o)
    o2: object = clumsy_1006(o1)
    o3: object = countTriples_1925(o2)
    o4: object = getMoneyAmount_375(o3)
    o5: object = lastRemaining_390(o4)
    return o5
