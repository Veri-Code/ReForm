from collections import Counter
from typing import Counter


def countLargestGroup_1399(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 8
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


def largestPalindrome_479(n: int) -> int:
    # input: 1 <= n <= 8
    # output: 1 <= <output> <= 2147483648
    mx = 10**n - 1
    for a in range(mx, mx // 10, -1):
        b = x = a
        while b:
            x = x * 10 + b % 10
            b //= 10
        t = mx
        while t * t >= x:
            if x % t == 0:
                return x % 1337
            t -= 1
    return 9


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: 1 <= <output> <= 100000000
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 0 <= <output> <= 100000000
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


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = countLargestGroup_1399(o)
    o2: object = largestPalindrome_479(o1)
    o3: object = smallestFactorization_625(o2)
    o4: object = maxDiff_1432(o3)
    o5: object = maximumSwap_670(o4)
    return o5
