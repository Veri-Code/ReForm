def clumsy_1006(n: int) -> int:
    # input: 1 <= n <= 10000
    # output: 1 <= <output> <= 2147483648
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


def smallestFactorization_625(num: int) -> int:
    # input: 1 <= num <= 2147483648
    # output: 1 <= <output> <= 2147483648
    if num < 2:
        return num
    (ans, mul) = (0, 1)
    for i in range(9, 1, -1):
        while num % i == 0:
            num //= i
            ans = mul * i + ans
            mul *= 10
    return ans if num < 2 and ans <= 2**31 - 1 else 0


def nextGreaterElement_556(n: int) -> int:
    # input: 1 <= n <= 2147483648
    # output: 1 <= <output> <= 100000
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


def numberOfWays_3183(n: int) -> int:
    # input: 1 <= n <= 100000
    # output: 1 <= <output> <= 1000
    mod = 10**9 + 7
    coins = [1, 2, 6]
    f = [0] * (n + 1)
    f[0] = 1
    for x in coins:
        for j in range(x, n + 1):
            f[j] = (f[j] + f[j - x]) % mod
    ans = f[n]
    if n >= 4:
        ans = (ans + f[n - 4]) % mod
    if n >= 8:
        ans = (ans + f[n - 8]) % mod
    return ans


def sumOfMultiples_2652(n: int) -> int:
    # input: 1 <= n <= 1000
    # output: unconstrained
    return sum((x for x in range(1, n + 1) if x % 3 == 0 or x % 5 == 0 or x % 7 == 0))


def main_5node_8(o: object) -> object:
    """5 nodes, single chain"""
    o1: object = clumsy_1006(o)
    o2: object = smallestFactorization_625(o1)
    o3: object = nextGreaterElement_556(o2)
    o4: object = numberOfWays_3183(o3)
    o5: object = sumOfMultiples_2652(o4)
    return o5
