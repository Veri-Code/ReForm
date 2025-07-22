def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 2 <= <output> <= 100000
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


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
    # output: 0 <= <output> <= 100000000

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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = sumOfMultiples_2652(o)
    o2: object = smallestValue_2507(o1)
    o3: object = primePalindrome_866(o2)
    o4: object = maximumSwap_670(o3)
    return o4
