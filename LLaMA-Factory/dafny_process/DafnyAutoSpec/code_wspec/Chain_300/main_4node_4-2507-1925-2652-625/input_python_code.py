from math import sqrt


def smallestValue_2507(n: int) -> int:
    # input: 2 <= n <= 100000
    # output: 1 <= <output> <= 250
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


def countTriples_1925(n: int) -> int:
    # input: 1 <= n <= 250
    # output: 1 <= <output> <= 1000
    ans = 0
    for a in range(1, n):
        for b in range(1, n):
            x = a * a + b * b
            c = int(sqrt(x))
            if c <= n and c * c == x:
                ans += 1
    return ans


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: 1 <= <output> <= 2147483648
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: unconstrained
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = smallestValue_2507(o)
    o2: object = countTriples_1925(o1)
    o3: object = sumOfMultiples_2652(o2)
    o4: object = smallestFactorization_625(o3)
    return o4
