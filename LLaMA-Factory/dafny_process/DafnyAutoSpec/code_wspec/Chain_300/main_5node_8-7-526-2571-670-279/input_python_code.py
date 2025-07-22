from collections import defaultdict
from math import sqrt

inf = float("inf")


def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: 1 <= <output> <= 15
    ans = 0
    (mi, mx) = (-(2**31), 2**31 - 1)
    while x:
        if ans < mi // 10 + 1 or ans > mx // 10:
            return 0
        y = x % 10
        if x < 0 and y > 0:
            y -= 10
        ans = ans * 10 + y
        x = (x - y) // 10
    return ans


def countArrangement_526(n: int) -> int:
    # input: 1 <= n <= 15
    # output: 1 <= <output> <= 100000

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


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 0 <= <output> <= 100000000
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


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: 1 <= <output> <= 10000
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


def numSquares_279(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: unconstrained
    m = int(sqrt(n))
    f = [[inf] * (n + 1) for _ in range(m + 1)]
    f[0][0] = 0
    for i in range(1, m + 1):
        for j in range(n + 1):
            f[i][j] = f[i - 1][j]
            if j >= i * i:
                f[i][j] = min(f[i][j], f[i][j - i * i] + 1)
    return f[m][n]


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = countArrangement_526(o1)
    o3: object = minOperations_2571(o2)
    o4: object = maximumSwap_670(o3)
    o5: object = numSquares_279(o4)
    return o5
