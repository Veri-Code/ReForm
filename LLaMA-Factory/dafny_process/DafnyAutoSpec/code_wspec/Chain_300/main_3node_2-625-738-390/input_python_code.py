def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: 0 <= <output> <= 1000000000
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def monotoneIncreasingDigits_738(n: int) -> int:
    # input: 0 <= n <= 1000000000
    # output: 1 <= <output> <= 1000000000
    s = list(str(n))
    i = 1
    while i < len(s) and s[i - 1] <= s[i]:
        i += 1
    if i < len(s):
        while i and s[i - 1] > s[i]:
            s[i - 1] = str(int(s[i - 1]) - 1)
            i -= 1
        i += 1
        while i < len(s):
            s[i] = "9"
            i += 1
    return int("".join(s))


def lastRemaining_390(n: int) -> int:
    # input: 1 <= n <= 1000000000
    # output: unconstrained
    (a1, an) = (1, n)
    (i, step, cnt) = (0, 1, n)
    while cnt > 1:
        if i % 2:
            an -= step
            if cnt % 2:
                a1 += step
        else:
            a1 += step
            if cnt % 2:
                an -= step
        cnt >>= 1
        step <<= 1
        i += 1
    return a1


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = smallestFactorization_625(o)
    o2: object = monotoneIncreasingDigits_738(o1)
    o3: object = lastRemaining_390(o2)
    return o3
