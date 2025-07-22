def largestPalindrome_479(n: int) -> int:
    # input: 1 <= n <= 8
    # output: 1 <= <output> <= 100000
    mx = 10**n - 1
    for a in range(mx, mx // 10, -1):
        b = x = a
        while b:
            x = x * 10 + b % 10
            b //= 10
        t = mx
        while t * t >= x:
            if x % t == 0:
                return x % 1337
            t -= 1
    return 9


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: -2147483648 <= <output> <= 2147483648
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = largestPalindrome_479(o)
    o2: object = numberOfWays_3183(o1)
    o3: object = reverse_7(o2)
    return o3
