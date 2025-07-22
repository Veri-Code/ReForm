def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: 1 <= <output> <= 2147483648

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


def integerReplacement_397(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: unconstrained
    ans = 0
    while n != 1:
        if n & 1 == 0:
            n >>= 1
        elif n != 3 and n & 3 == 3:
            n += 1
        else:
            n -= 1
        ans += 1
    return ans


def main_2node_1(o: object) -> object:
    """2 nodes, single chain"""
    o1: object = primePalindrome_866(o)
    o2: object = integerReplacement_397(o1)
    return o2
