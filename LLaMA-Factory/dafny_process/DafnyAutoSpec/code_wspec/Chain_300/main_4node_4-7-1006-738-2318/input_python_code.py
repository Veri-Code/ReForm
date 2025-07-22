from math import gcd


def reverse_7(x: int) -> int:
    # input: -2147483648 <= x <= 2147483648
    # output: 1 <= <output> <= 10000
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


def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 0 <= <output> <= 1000000000
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


def monotoneIncreasingDigits_738(n: int) -> int:
    # input: 0 <= n <= 1000000000
    # output: 1 <= <output> <= 10000
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


def distinctSequences_2318(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: unconstrained
    if n == 1:
        return 6
    mod = 10**9 + 7
    dp = [[[0] * 6 for _ in range(6)] for _ in range(n + 1)]
    for i in range(6):
        for j in range(6):
            if gcd(i + 1, j + 1) == 1 and i != j:
                dp[2][i][j] = 1
    for k in range(3, n + 1):
        for i in range(6):
            for j in range(6):
                if gcd(i + 1, j + 1) == 1 and i != j:
                    for h in range(6):
                        if gcd(h + 1, i + 1) == 1 and h != i and (h != j):
                            dp[k][i][j] += dp[k - 1][h][i]
    ans = 0
    for i in range(6):
        for j in range(6):
            ans += dp[-1][i][j]
    return ans % mod


def main_4node_4(o: object) -> object:
    """4 nodes, single chain"""
    o1: object = reverse_7(o)
    o2: object = clumsy_1006(o1)
    o3: object = monotoneIncreasingDigits_738(o2)
    o4: object = distinctSequences_2318(o3)
    return o4
