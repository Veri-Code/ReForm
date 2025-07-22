def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 1 <= <output> <= 8
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


def largestPalindrome_479(n: int) -> int:
    # input: 1 <= n <= 8
    # output: 1 <= <output> <= 1000
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


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: unconstrained
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = maxDiff_1432(o)
    o2: object = largestPalindrome_479(o1)
    o3: object = sumOfMultiples_2652(o2)
    return o3
