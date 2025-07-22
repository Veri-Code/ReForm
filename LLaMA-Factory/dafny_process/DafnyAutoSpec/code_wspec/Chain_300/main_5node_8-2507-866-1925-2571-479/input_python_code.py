from math import sqrt


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 100000000
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


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: 1 <= <output> <= 250

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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 100000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 8
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


def largestPalindrome_479(n: int) -> int:
    # input: 1 <= n <= 8
    # output: unconstrained
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


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = smallestValue_2507(o)
    o2: object = primePalindrome_866(o1)
    o3: object = countTriples_1925(o2)
    o4: object = minOperations_2571(o3)
    o5: object = largestPalindrome_479(o4)
    return o5
