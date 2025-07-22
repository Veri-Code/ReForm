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
    # output: 1 <= <output> <= 100000
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


def minOperations_2571(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: unconstrained
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


def main_3node_2(o: object) -> object:
    """3 nodes, single chain"""
    o1: object = smallestFactorization_625(o)
    o2: object = monotoneIncreasingDigits_738(o1)
    o3: object = minOperations_2571(o2)
    return o3
