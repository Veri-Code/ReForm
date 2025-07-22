from math import sqrt
from operator import abs

inf = float("inf")


def numSquares_279(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 2 <= <output> <= 100000
    m = int(sqrt(n))
    f = [[inf] * (n + 1) for _ in range(m + 1)]
    f[0][0] = 0
    for i in range(1, m + 1):
        for j in range(n + 1):
            f[i][j] = f[i - 1][j]
            if j >= i * i:
                f[i][j] = min(f[i][j], f[i][j - i * i] + 1)
    return f[m][n]


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: -1000000000000000 <= <output> <= 1000000000000000
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


def smallestNumber_2165(num: int) -> int:
    # input: -1000000000000000 <= num <= 1000000000000000
    # output: 1 <= <output> <= 2147483648
    neg = num < 0
    num = abs(num)
    cnt = [0] * 10
    while num:
        cnt[num % 10] += 1
        num //= 10
    ans = 0
    if neg:
        for i in reversed(range(10)):
            for _ in range(cnt[i]):
                ans *= 10
                ans += i
        return -ans
    if cnt[0]:
        for i in range(1, 10):
            if cnt[i]:
                ans = i
                cnt[i] -= 1
                break
    for i in range(10):
        for _ in range(cnt[i]):
            ans *= 10
            ans += i
    return ans


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: unconstrained
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = numSquares_279(o)
    o2: object = smallestValue_2507(o1)
    o3: object = smallestNumber_2165(o2)
    o4: object = integerReplacement_397(o3)
    return o4
