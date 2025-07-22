from operator import abs


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 1 <= <output> <= 1000000000
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def closestFair_2417(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: -1000000000000000 <= <output> <= 1000000000000000
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = sumOfMultiples_2652(o)
    o2: object = closestFair_2417(o1)
    o3: object = smallestNumber_2165(o2)
    return o3
