def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 100000000
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
    # output: 1 <= <output> <= 10000
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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: unconstrained
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = nextGreaterElement_556(o)
    o2: object = maxDiff_1432(o1)
    o3: object = lastRemaining_390(o2)
    o4: object = clumsy_1006(o3)
    return o4
