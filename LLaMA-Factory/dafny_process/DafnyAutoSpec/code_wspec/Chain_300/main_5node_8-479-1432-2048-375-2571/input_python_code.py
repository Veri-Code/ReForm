from itertools import count


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
    # output: 0 <= <output> <= 1000000
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


def nextBeautifulNumber_2048(n: int) -> int:
    # input: 0 <= n <= 1000000
    # output: 1 <= <output> <= 200
    for x in count(n + 1):
        y = x
        cnt = [0] * 10
        while y:
            (y, v) = divmod(y, 10)
            cnt[v] += 1
        if all((v == 0 or i == v for (i, v) in enumerate(cnt))):
            return x


def getMoneyAmount_375(n: int) -> int:
    # input: 1 <= n <= 200
    # output: 1 <= <output> <= 100000
    f = [[0] * (n + 1) for _ in range(n + 1)]
    for i in range(n - 1, 0, -1):
        for j in range(i + 1, n + 1):
            f[i][j] = j + f[i][j - 1]
            for k in range(i, j):
                f[i][j] = min(f[i][j], max(f[i][k - 1], f[k + 1][j]) + k)
    return f[1][n]


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


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = largestPalindrome_479(o)
    o2: object = maxDiff_1432(o1)
    o3: object = nextBeautifulNumber_2048(o2)
    o4: object = getMoneyAmount_375(o3)
    o5: object = minOperations_2571(o4)
    return o5
