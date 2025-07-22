from collections import defaultdict


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 100000000
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


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 1 <= <output> <= 15
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


def countArrangement_526(n: int) -> int:
    # input: 1 <= n <= 15
    # output: 1 <= <output> <= 1000000000

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


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 100000000
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


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: unconstrained

    def is_prime(x):
        if x < 2:
            return False
        v = 2
        while v * v <= x:
            if x % v == 0:
                return False
            v += 1
        return True

    def reverse(x):
        res = 0
        while x:
            res = res * 10 + x % 10
            x //= 10
        return res

    while 1:
        if reverse(n) == n and is_prime(n):
            return n
        if 10**7 < n < 10**8:
            n = 10**8
        n += 1


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = clumsy_1006(o)
    o2: object = maxDiff_1432(o1)
    o3: object = countArrangement_526(o2)
    o4: object = lastRemaining_390(o3)
    o5: object = primePalindrome_866(o4)
    return o5
