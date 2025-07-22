def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: 2 <= <output> <= 100000
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


def main_2node_1(o: object) -> object:
    """2 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = smallestValue_2507(o1)
    return o2
