from math import sqrt

inf = float("inf")


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 10000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


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


def main_2node_1(o: object) -> object:
    """2 nodes, single chain"""
    o1: object = countTriples_1925(o)
    o2: object = numSquares_279(o1)
    return o2
