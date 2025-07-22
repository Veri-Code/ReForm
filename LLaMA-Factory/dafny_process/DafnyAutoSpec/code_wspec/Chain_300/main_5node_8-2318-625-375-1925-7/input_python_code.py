from math import gcd
from math import sqrt


def distinctSequences_2318(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 2147483648
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


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: 1 <= <output> <= 200
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def getMoneyAmount_375(n: int) -> int:
    # input: 1 <= n <= 200
    # output: 1 <= <output> <= 250
    f = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(n - 1, 0, -1):
        for j in range(i + 1, n + 1):
            f[i][j] = j + f[i][j - 1]
            for k in range(i, j):
                f[i][j] = min(f[i][j], max(f[i][k - 1], f[k + 1][j]) + k)
    return f[1][n]


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: -2147483648 <= <output> <= 2147483648
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: unconstrained
    ans = 0
    (mi, mx) = (-(2**31), 2**31 - 1)
    while x:
        if ans < mi // 10 + 1 or ans > mx // 10:
            return 0
        y = x % 10
        if x < 0 and y > 0:
            y -= 10
        ans = ans * 10 + y
        x = (x - y) // 10
    return ans


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = distinctSequences_2318(o)
    o2: object = smallestFactorization_625(o1)
    o3: object = getMoneyAmount_375(o2)
    o4: object = countTriples_1925(o3)
    o5: object = reverse_7(o4)
    return o5
