from math import sqrt


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: 1 <= <output> <= 100000000
    s = list(str(num))
    n = len(s)
    d = list(range(n))
    for i in range(n - 2, -1, -1):
        if s[i] <= s[d[i + 1]]:
            d[i] = d[i + 1]
    for i, j in enumerate(d):
        if s[i] < s[j]:
            (s[i], s[j]) = (s[j], s[i])
            break
    return int("".join(s))


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


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 250
    (a1, an) = (1, n)
    (i, step, cnt) = (0, 1, n)
    while cnt > 1:
        if i % 2:
            an -= step
            if cnt % 2:
                a1 += step
        else:
            a1 += step
            if cnt % 2:
                an -= step
        cnt >>= 1
        step <<= 1
        i += 1
    return a1


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
    o1: object = maximumSwap_670(o)
    o2: object = maxDiff_1432(o1)
    o3: object = lastRemaining_390(o2)
    o4: object = countTriples_1925(o3)
    return o4
