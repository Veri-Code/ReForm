from itertools import count


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
    # output: 1 <= <output> <= 1000000000
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


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 2147483648
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


def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 0 <= <output> <= 1000000
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


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: unconstrained
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = lastRemaining_390(o1)
    o3: object = closestFair_2417(o2)
    o4: object = nextGreaterElement_556(o3)
    o5: object = nextBeautifulNumber_2048(o4)
    return o5
