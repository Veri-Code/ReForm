from collections import defaultdict
from math import sqrt


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: 1 <= <output> <= 250
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 15
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def countArrangement_526(n: int) -> int:
    # input: 1 <= n <= 15
    # output: 1 <= <output> <= 100000

    def dfs(i):
        nonlocal ans, n
        if i == n + 1:
            ans += 1
            return
        for j in match[i]:
            if not vis[j]:
                vis[j] = True
                dfs(i + 1)
                vis[j] = False

    ans = 0
    vis = [False] * (n + 1)
    match = defaultdict(list)
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            if j % i == 0 or i % j == 0:
                match[i].append(j)
    dfs(1)
    return ans


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 1000
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


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: unconstrained
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = smallestFactorization_625(o)
    o2: object = countTriples_1925(o1)
    o3: object = countArrangement_526(o2)
    o4: object = minOperations_2571(o3)
    o5: object = sumOfMultiples_2652(o4)
    return o5
