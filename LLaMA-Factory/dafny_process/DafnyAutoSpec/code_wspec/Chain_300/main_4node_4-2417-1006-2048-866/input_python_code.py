from itertools import count


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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 0 <= <output> <= 1000000
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


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: 1 <= <output> <= 100000000
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: unconstrained

    def is_prime(x):
        if x < 2:
            return False
        v = 2
        while v * v <= x:
            if x % v == 0:
                return False
            v += 1
        return True

    def reverse(x):
        res = 0
        while x:
            res = res * 10 + x % 10
            x //= 10
        return res

    while 1:
        if reverse(n) == n and is_prime(n):
            return n
        if 10**7 < n < 10**8:
            n = 10**8
        n += 1


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = closestFair_2417(o)
    o2: object = clumsy_1006(o1)
    o3: object = nextBeautifulNumber_2048(o2)
    o4: object = primePalindrome_866(o3)
    return o4
