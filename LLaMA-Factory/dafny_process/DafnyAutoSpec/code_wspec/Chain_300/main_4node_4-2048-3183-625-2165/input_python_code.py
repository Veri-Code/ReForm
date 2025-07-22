from itertools import count
from operator import abs


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: 1 <= <output> <= 100000
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 2147483648
    mod = 10**9 + 7
    coins = [1, 2, 6]
    f = [0] * (n + 1)
    f[0] = 1
    for x in coins:
        for j in range(x, n + 1):
            f[j] = (f[j] + f[j - x]) % mod
    ans = f[n]
    if n >= 4:
        ans = (ans + f[n - 4]) % mod
    if n >= 8:
        ans = (ans + f[n - 8]) % mod
    return ans


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: -1000000000000000 <= <output> <= 1000000000000000
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = nextBeautifulNumber_2048(o)
    o2: object = numberOfWays_3183(o1)
    o3: object = smallestFactorization_625(o2)
    o4: object = smallestNumber_2165(o3)
    return o4
