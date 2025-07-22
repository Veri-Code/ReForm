from itertools import count
from math import sqrt
from operator import abs


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 1000000000
    ans = cnt = 0
    while n:
        if n & 1:
            cnt += 1
        elif cnt:
            ans += 1
            cnt = 0 if cnt == 1 else 1
        n >>= 1
    if cnt == 1:
        ans += 1
    elif cnt > 1:
        ans += 2
    return ans


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: 1 <= <output> <= 250
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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 0 <= <output> <= 1000000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: -1000000000000000 <= <output> <= 1000000000000000
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def smallestNumber_2165(num: int) -> int:
    # input: -1000000000000000 <= num <= 1000000000000000
    # output: unconstrained
    neg = num < 0
    num = abs(num)
    cnt = [0] * 10
    while num:
        cnt[num % 10] += 1
        num //= 10
    ans = 0
    if neg:
        for i in reversed(range(10)):
            for _ in range(cnt[i]):
                ans *= 10
                ans += i
        return -ans
    if cnt[0]:
        for i in range(1, 10):
            if cnt[i]:
                ans = i
                cnt[i] -= 1
                break
    for i in range(10):
        for _ in range(cnt[i]):
            ans *= 10
            ans += i
    return ans


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = minOperations_2571(o)
    o2: object = lastRemaining_390(o1)
    o3: object = countTriples_1925(o2)
    o4: object = nextBeautifulNumber_2048(o3)
    o5: object = smallestNumber_2165(o4)
    return o5
