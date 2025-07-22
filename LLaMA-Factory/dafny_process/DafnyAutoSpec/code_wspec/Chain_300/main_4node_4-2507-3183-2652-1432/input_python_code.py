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


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 1000
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


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 1 <= <output> <= 100000000
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: unconstrained
    (a, b) = (str(num), str(num))
    for c in a:
        if c != "9":
            a = a.replace(c, "9")
            break
    if b[0] != "1":
        b = b.replace(b[0], "1")
    else:
        for c in b[1:]:
            if c not in "01":
                b = b.replace(c, "0")
                break
    return int(a) - int(b)


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = smallestValue_2507(o)
    o2: object = numberOfWays_3183(o1)
    o3: object = sumOfMultiples_2652(o2)
    o4: object = maxDiff_1432(o3)
    return o4
