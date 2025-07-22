from itertools import count
from math import sqrt


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 2147483648
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: 0 <= <output> <= 1000000
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = countTriples_1925(o)
    o2: object = smallestFactorization_625(o1)
    o3: object = nextBeautifulNumber_2048(o2)
    return o3
