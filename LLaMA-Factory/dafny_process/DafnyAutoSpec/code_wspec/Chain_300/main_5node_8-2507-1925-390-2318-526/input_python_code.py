from collections import defaultdict
from math import gcd
from math import sqrt


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 250
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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 1000000000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 10000
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


def distinctSequences_2318(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 15
    if n == 1:
        return 6
    mod = 10**9 + 7
    dp = [[[0] * 6 for _ in range(6)] for _ in range(n + 1)]
    for i in range(6):
        for j in range(6):
            if gcd(i + 1, j + 1) == 1 and i != j:
                dp[2][i][j] = 1
    for k in range(3, n + 1):
        for i in range(6):
            for j in range(6):
                if gcd(i + 1, j + 1) == 1 and i != j:
                    for h in range(6):
                        if gcd(h + 1, i + 1) == 1 and h != i and (h != j):
                            dp[k][i][j] += dp[k - 1][h][i]
    ans = 0
    for i in range(6):
        for j in range(6):
            ans += dp[-1][i][j]
    return ans % mod


def countArrangement_526(n: int) -> int:
    # input: 1 <= n <= 15
    # output: unconstrained

    def dfs(i):
        nonlocal ans, n
        if i == n + 1:
            ans += 1
            return
        for j in match[i]:
            if not vis[j]:
                vis[j] = True
                dfs(i + 1)
                vis[j] = False

    ans = 0
    vis = [False] * (n + 1)
    match = defaultdict(list)
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if j % i == 0 or i % j == 0:
                match[i].append(j)
    dfs(1)
    return ans


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = smallestValue_2507(o)
    o2: object = countTriples_1925(o1)
    o3: object = lastRemaining_390(o2)
    o4: object = distinctSequences_2318(o3)
    o5: object = countArrangement_526(o4)
    return o5
