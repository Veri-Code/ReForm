def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: 1 <= <output> <= 100000
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


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: unconstrained
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


def main_2node_1(o: object) -> object:
    """2 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = numberOfWays_3183(o1)
    return o2
