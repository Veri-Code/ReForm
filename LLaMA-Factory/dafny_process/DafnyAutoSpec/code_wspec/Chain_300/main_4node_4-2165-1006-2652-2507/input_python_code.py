from operator import abs


def smallestNumber_2165(num: int) -> int:
    # input: -1000000000000000 <= num <= 1000000000000000
    # output: 1 <= <output> <= 10000
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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 1000
    k = 0
    stk = [n]
    for x in range(n - 1, 0, -1):
        if k == 0:
            stk.append(stk.pop() * x)
        elif k == 1:
            stk.append(int(stk.pop() / x))
        elif k == 2:
            stk.append(x)
        else:
            stk.append(-x)
        k = (k + 1) % 4
    return sum(stk)


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 2 <= <output> <= 100000
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: unconstrained
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = smallestNumber_2165(o)
    o2: object = clumsy_1006(o1)
    o3: object = sumOfMultiples_2652(o2)
    o4: object = smallestValue_2507(o3)
    return o4
