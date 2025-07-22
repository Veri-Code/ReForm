from math import sqrt

inf = float("inf")


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 1000000000
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


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 2147483648
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


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 100000000
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


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: 1 <= <output> <= 10000

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
    o1: object = clumsy_1006(o)
    o2: object = lastRemaining_390(o1)
    o3: object = integerReplacement_397(o2)
    o4: object = primePalindrome_866(o3)
    o5: object = numSquares_279(o4)
    return o5
