from itertools import count


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: 1 <= <output> <= 2147483648
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 0 <= <output> <= 100000000
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


def maximumSwap_670(num: int) -> int:
    # input: 0 <= num <= 100000000
    # output: unconstrained
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = nextBeautifulNumber_2048(o)
    o2: object = integerReplacement_397(o1)
    o3: object = maximumSwap_670(o2)
    return o3
