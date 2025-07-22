from collections import Counter
from typing import Counter


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 10000
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


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 2147483648
    cnt = Counter()
    ans = mx = 0
    for i in range(1, n + 1):
        s = 0
        while i:
            s += i % 10
            i //= 10
        cnt[s] += 1
        if mx < cnt[s]:
            mx = cnt[s]
            ans = 1
        elif mx == cnt[s]:
            ans += 1
    return ans


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: unconstrained
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = closestFair_2417(o)
    o2: object = countLargestGroup_1399(o1)
    o3: object = smallestFactorization_625(o2)
    return o3
