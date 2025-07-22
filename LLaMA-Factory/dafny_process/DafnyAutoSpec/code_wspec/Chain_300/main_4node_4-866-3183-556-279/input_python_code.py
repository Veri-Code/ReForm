from math import sqrt

inf = float("inf")


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: 1 <= <output> <= 100000

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


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 2147483648
    mod = 10**9 + 7
    coins = [1, 2, 6]
    f = [0] * (n + 1)
    f[0] = 1
    for x in coins:
        for j in range(x, n + 1):
            f[j] = (f[j] + f[j - x]) % mod
    ans = f[n]
    if n >= 4:
        ans = (ans + f[n - 4]) % mod
    if n >= 8:
        ans = (ans + f[n - 8]) % mod
    return ans


def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 10000
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = primePalindrome_866(o)
    o2: object = numberOfWays_3183(o1)
    o3: object = nextGreaterElement_556(o2)
    o4: object = numSquares_279(o3)
    return o4
