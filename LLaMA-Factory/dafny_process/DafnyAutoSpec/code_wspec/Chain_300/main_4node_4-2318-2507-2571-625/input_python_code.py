from math import gcd


def distinctSequences_2318(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 2 <= <output> <= 100000
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


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 100000
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


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 2147483648
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


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: unconstrained
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = distinctSequences_2318(o)
    o2: object = smallestValue_2507(o1)
    o3: object = minOperations_2571(o2)
    o4: object = smallestFactorization_625(o3)
    return o4
