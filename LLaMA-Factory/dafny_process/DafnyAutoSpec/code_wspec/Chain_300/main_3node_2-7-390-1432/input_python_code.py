def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: 1 <= <output> <= 1000000000
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


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 100000000
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = lastRemaining_390(o1)
    o3: object = maxDiff_1432(o2)
    return o3
