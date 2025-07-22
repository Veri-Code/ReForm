from math import sqrt

inf = float("inf")


def numSquares_279(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 0 <= <output> <= 1000000000
    m = int(sqrt(n))
    f = [[inf] * (n + 1) for _ in range(m + 1)]
    f[0][0] = 0
    for i in range(1, m + 1):
        for j in range(n + 1):
            f[i][j] = f[i - 1][j]
            if j >= i * i:
                f[i][j] = min(f[i][j], f[i][j - i * i] + 1)
    return f[m][n]


def monotoneIncreasingDigits_738(n: int) -> int:
    # input: 0 <= n <= 1000000000
    # output: 1 <= <output> <= 2147483648
    s = list(str(n))
    i = 1
    while i < len(s) and s[i - 1] <= s[i]:
        i += 1
    if i < len(s):
        while i and s[i - 1] > s[i]:
            s[i - 1] = str(int(s[i - 1]) - 1)
            i -= 1
        i += 1
        while i < len(s):
            s[i] = "9"
            i += 1
    return int("".join(s))


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 100000
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


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 200
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


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = numSquares_279(o)
    o2: object = monotoneIncreasingDigits_738(o1)
    o3: object = integerReplacement_397(o2)
    o4: object = minOperations_2571(o3)
    o5: object = getMoneyAmount_375(o4)
    return o5
