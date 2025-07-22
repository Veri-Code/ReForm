def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: 1 <= <output> <= 100000000
    ans = 0
    (mi, mx) = (-(2**31), 2**31 - 1)
    while x:
        if ans < mi // 10 + 1 or ans > mx // 10:
            return 0
        y = x % 10
        if x < 0 and y > 0:
            y -= 10
        ans = ans * 10 + y
        x = (x - y) // 10
    return ans


def primePalindrome_866(n: int) -> int:
    # input: 1 <= n <= 100000000
    # output: 1 <= <output> <= 8

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


def largestPalindrome_479(n: int) -> int:
    # input: 1 <= n <= 8
    # output: 1 <= <output> <= 100000000
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


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: unconstrained
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


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = primePalindrome_866(o1)
    o3: object = largestPalindrome_479(o2)
    o4: object = maxDiff_1432(o3)
    return o4
