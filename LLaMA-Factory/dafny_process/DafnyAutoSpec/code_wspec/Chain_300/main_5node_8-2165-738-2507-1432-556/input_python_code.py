from operator import abs


def smallestNumber_2165(num: int) -> int:
    # input: -1000000000000000 <= num <= 1000000000000000
    # output: 0 <= <output> <= 1000000000
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


def monotoneIncreasingDigits_738(n: int) -> int:
    # input: 0 <= n <= 1000000000
    # output: 2 <= <output> <= 100000
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


def maxDiff_1432(num: int) -> int:
    # input: 1 <= num <= 100000000
    # output: 1 <= <output> <= 2147483648
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


def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: unconstrained
    cs = list(str(n))
    n = len(cs)
    (i, j) = (n - 2, n - 1)
    while i >= 0 and cs[i] >= cs[i + 1]:
        i -= 1
    if i < 0:
        return -1
    while cs[i] >= cs[j]:
        j -= 1
    (cs[i], cs[j]) = (cs[j], cs[i])
    cs[i + 1 :] = cs[i + 1 :][::-1]
    ans = int("".join(cs))
    return -1 if ans > 2**31 - 1 else ans


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = smallestNumber_2165(o)
    o2: object = monotoneIncreasingDigits_738(o1)
    o3: object = smallestValue_2507(o2)
    o4: object = maxDiff_1432(o3)
    o5: object = nextGreaterElement_556(o4)
    return o5
