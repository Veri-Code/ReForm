from math import gcd
from math import sqrt


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: 2 <= <output> <= 100000

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


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 10000
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


def distinctSequences_2318(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 250
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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: unconstrained
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = primePalindrome_866(o)
    o2: object = smallestValue_2507(o1)
    o3: object = distinctSequences_2318(o2)
    o4: object = countTriples_1925(o3)
    return o4
