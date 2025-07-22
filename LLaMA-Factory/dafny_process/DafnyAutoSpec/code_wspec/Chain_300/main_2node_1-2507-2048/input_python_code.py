from itertools import count


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 0 <= <output> <= 1000000
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
    o1: object = smallestValue_2507(o)
    o2: object = nextBeautifulNumber_2048(o1)
    return o2
