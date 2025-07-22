def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 2147483648
    cs = list(str(n))
    n = len(cs)
    (i, j) = (n - 2, n - 1)
    while i >= 0 and cs[i] >= cs[i + 1]:
        i -= 1
    if i < 0:
        return -1
    while cs[i] >= cs[j]:
        j -= 1
    (cs[i], cs[j]) = (cs[j], cs[i])
    cs[i + 1 :] = cs[i + 1 :][::-1]
    ans = int("".join(cs))
    return -1 if ans > 2**31 - 1 else ans


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 100000
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


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 1000000000
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


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: unconstrained
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = nextGreaterElement_556(o)
    o2: object = integerReplacement_397(o1)
    o3: object = numberOfWays_3183(o2)
    o4: object = closestFair_2417(o3)
    return o4
