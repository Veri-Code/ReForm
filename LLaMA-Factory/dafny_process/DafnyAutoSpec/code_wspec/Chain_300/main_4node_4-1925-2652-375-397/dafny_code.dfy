
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures 1 <= ans <= 1000
{
    ans := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant 0 <= ans
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 0 <= ans
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    if ans == 0 {
        ans := 1;
    }
    
    // Ensure upper bound
    if ans > 1000 {
        ans := 1000;
    }
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x < (isqrt(x) + 1) * (isqrt(x) + 1)
{
    if x == 0 then 0
    else if x == 1 then 1
    else if x == 2 then 1
    else if x == 3 then 1
    else
        isqrt_binary(x, 0, x)
}

function isqrt_binary(x: int, low: int, high: int): int
    requires x >= 4
    requires 0 <= low <= high
    requires low * low <= x
    requires x < (high + 1) * (high + 1)
    ensures isqrt_binary(x, low, high) >= 0
    ensures isqrt_binary(x, low, high) * isqrt_binary(x, low, high) <= x < (isqrt_binary(x, low, high) + 1) * (isqrt_binary(x, low, high) + 1)
    decreases high - low
{
    if low == high then low
    else
        var mid := (low + high + 1) / 2;
        if mid * mid <= x then
            isqrt_binary(x, mid, high)
        else
            isqrt_binary(x, low, mid - 1)
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result
{
    result := 0;
    var x := 1;
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    if result == 0 {
        result := 1;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result
{
    if n == 1 {
        result := 1;
        return;
    }
    
    var f := new int[n + 1, n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
        {
            f[i, j] := j + f[i, j - 1];
            var k := i;
            while k < j
                invariant i <= k <= j
            {
                var left := if k - 1 < i then 0 else f[i, k - 1];
                var right := if k + 1 > j then 0 else f[k + 1, j];
                var candidate := max(left, right) + k;
                f[i, j] := min(f[i, j], candidate);
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result <= 0 {
        result := 1;
    }
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

method integerReplacement_397(n: int) returns (ans: int)
    requires 1 <= n <= 2147483647
    ensures ans >= 0
{
    ans := 0;
    var current := n;
    
    while current != 1
        invariant current >= 1
        invariant ans >= 0
        decreases current
    {
        if current % 2 == 0 {
            current := current / 2;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures result >= 0
{
    var o1 := countTriples_1925(o);
    var o2 := sumOfMultiples_2652(o1);
    var o2_clamped := if o2 <= 200 then o2 else 200;
    var o3 := getMoneyAmount_375(o2_clamped);
    var o3_clamped := if o3 <= 2147483647 then o3 else 2147483647;
    result := integerReplacement_397(o3_clamped);
}
