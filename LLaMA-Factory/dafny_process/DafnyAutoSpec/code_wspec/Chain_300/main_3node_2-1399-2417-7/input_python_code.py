from collections import Counter
from typing import Counter


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 1000000000
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


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: -2147483648 <= <output> <= 2147483648
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


def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: unconstrained
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = countLargestGroup_1399(o)
    o2: object = closestFair_2417(o1)
    o3: object = reverse_7(o2)
    return o3
