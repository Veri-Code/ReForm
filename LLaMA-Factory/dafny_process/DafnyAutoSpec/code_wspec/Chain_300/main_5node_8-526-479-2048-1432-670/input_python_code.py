from collections import defaultdict
from itertools import count


def countArrangement_526(n: int) -> int:
    # input: 1 <= n <= 15
    # output: 1 <= <output> <= 8

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


def largestPalindrome_479(n: int) -> int:
    # input: 1 <= n <= 8
    # output: 0 <= <output> <= 1000000
    mx = 10**n - 1
    for a in range(mx, mx // 10, -1):
        b = x = a
        while b:
            x = x * 10 + b % 10
            b //= 10
        t = mx
        while t * t >= x:
            if x % t == 0:
                return x % 1337
            t -= 1
    return 9


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: 1 <= <output> <= 100000000
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 0 <= <output> <= 100000000
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


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: unconstrained
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


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = countArrangement_526(o)
    o2: object = largestPalindrome_479(o1)
    o3: object = nextBeautifulNumber_2048(o2)
    o4: object = maxDiff_1432(o3)
    o5: object = maximumSwap_670(o4)
    return o5
