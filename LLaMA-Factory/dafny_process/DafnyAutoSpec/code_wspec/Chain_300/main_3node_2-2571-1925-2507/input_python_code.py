from math import sqrt


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 250
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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 2 <= <output> <= 100000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: unconstrained
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = minOperations_2571(o)
    o2: object = countTriples_1925(o1)
    o3: object = smallestValue_2507(o2)
    return o3
