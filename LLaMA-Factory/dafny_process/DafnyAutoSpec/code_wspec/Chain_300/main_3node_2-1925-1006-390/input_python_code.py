from math import sqrt


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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 1000000000
    k = 0
    stk = [n]
    for x in range(n - 1, 0, -1):
        if k == 0:
            stk.append(stk.pop() * x)
        elif k == 1:
            stk.append(int(stk.pop() / x))
        elif k == 2:
            stk.append(x)
        else:
            stk.append(-x)
        k = (k + 1) % 4
    return sum(stk)


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: unconstrained
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = countTriples_1925(o)
    o2: object = clumsy_1006(o1)
    o3: object = lastRemaining_390(o2)
    return o3
