from math import sqrt

inf = float("inf")


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 10000
    a = b = k = 0
    t = n
    while t:
        if t % 10 & 1:
            a += 1
        else:
            b += 1
        t //= 10
        k += 1
    if k & 1:
        x = 10**k
        y = int("1" * (k >> 1) or "0")
        return x + y
    if a == b:
        return n
    return closestFair_2417(n + 1)


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 200
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


def getMoneyAmount_375(n: int) -> int:
    # input: 1 <= n <= 200
    # output: 1 <= <output> <= 10000
    f = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(n - 1, 0, -1):
        for j in range(i + 1, n + 1):
            f[i][j] = j + f[i][j - 1]
            for k in range(i, j):
                f[i][j] = min(f[i][j], max(f[i][k - 1], f[k + 1][j]) + k)
    return f[1][n]


def numSquares_279(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 100000000
    m = int(sqrt(n))
    f = [[inf] * (n + 1) for _ in range(m + 1)]
    f[0][0] = 0
    for i in range(1, m + 1):
        for j in range(n + 1):
            f[i][j] = f[i - 1][j]
            if j >= i * i:
                f[i][j] = min(f[i][j], f[i][j - i * i] + 1)
    return f[m][n]


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
    o1: object = closestFair_2417(o)
    o2: object = clumsy_1006(o1)
    o3: object = getMoneyAmount_375(o2)
    o4: object = numSquares_279(o3)
    o5: object = primePalindrome_866(o4)
    return o5
