from itertools import count


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


def main_2node_1(o: object) -> object:
    """2 nodes, single chain"""
    o1: object = nextGreaterElement_556(o)
    o2: object = nextBeautifulNumber_2048(o1)
    return o2
