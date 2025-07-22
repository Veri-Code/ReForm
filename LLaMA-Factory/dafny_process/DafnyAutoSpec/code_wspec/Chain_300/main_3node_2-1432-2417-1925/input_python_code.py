from math import sqrt


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 1 <= <output> <= 1000000000
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


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 250
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = maxDiff_1432(o)
    o2: object = closestFair_2417(o1)
    o3: object = countTriples_1925(o2)
    return o3
