from collections import defaultdict
from math import sqrt


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: 1 <= <output> <= 250
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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 2147483648
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 15
    cs = list(str(n))
    n = len(cs)
    (i, j) = (n - 2, n - 1)
    while i >= 0 and cs[i] >= cs[i + 1]:
        i -= 1
    if i < 0:
        return -1
    while cs[i] >= cs[j]:
        j -= 1
    (cs[i], cs[j]) = (cs[j], cs[i])
    cs[i + 1 :] = cs[i + 1 :][::-1]
    ans = int("".join(cs))
    return -1 if ans > 2**31 - 1 else ans


def countArrangement_526(n: int) -> int:
    # input: 1 <= n <= 15
    # output: 1 <= <output> <= 10000

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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: unconstrained
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


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = maximumSwap_670(o)
    o2: object = countTriples_1925(o1)
    o3: object = nextGreaterElement_556(o2)
    o4: object = countArrangement_526(o3)
    o5: object = clumsy_1006(o4)
    return o5
