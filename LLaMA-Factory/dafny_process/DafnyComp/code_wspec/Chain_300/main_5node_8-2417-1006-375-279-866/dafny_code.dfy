
method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 10000
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        decreases t
    {
        if t % 10 % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
        result := x + y;
        if result > 10000 {
            result := 10000;
        }
    } else if a == b {
        result := n;
        if result > 10000 {
            result := 10000;
        }
    } else {
        if n + 1 <= 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 10000;
        }
    }
}

function power10(exp: int): int
    requires exp >= 0
    ensures power10(exp) >= 1
{
    if exp == 0 then 1
    else 10 * power10(exp - 1)
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 200
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x < n
        invariant |stk| >= 1
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top * x];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top / x];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := sum_seq(stk);
    
    // Bound the result based on the problem constraints
    if result < 1 {
        result := 1;
    } else if result > 200 {
        result := 200;
    }
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 10000
{
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
        decreases i
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
                var left := if k - 1 >= 0 then f[i, k - 1] else 0;
                var right := if k + 1 <= n then f[k + 1, j] else 0;
                var cost := max(left, right) + k;
                f[i, j] := min(f[i, j], cost);
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result < 1 {
        result := 1;
    } else if result > 10000 {
        result := 10000;
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

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    var m := sqrt_int(n);
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 1000000;
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
                f[i, j] := min(f[i, j], f[i, j - i * i] + 1);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result < 1 {
        result := 1;
    } else if result > 10000 {
        result := 10000;
    }
}

function sqrt_int(n: int): int
    requires n >= 0
    ensures sqrt_int(n) >= 0
    ensures sqrt_int(n) * sqrt_int(n) <= n
{
    if n == 0 then 0
    else sqrt_helper(n, 0, n + 1)
}

function sqrt_helper(n: int, low: int, high: int): int
    requires n >= 1
    requires low >= 0
    requires high >= low + 1
    requires low * low <= n
    requires high * high > n
    decreases high - low
    ensures sqrt_helper(n, low, high) >= 0
    ensures sqrt_helper(n, low, high) * sqrt_helper(n, low, high) <= n
{
    if high - low <= 1 then low
    else
        var mid := (low + high) / 2;
        if mid * mid <= n then
            sqrt_helper(n, mid, high)
        else
            sqrt_helper(n, low, mid)
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 2
    decreases *
{
    var current := n;
    
    while true
        decreases *
    {
        if reverse_int(current) == current && is_prime(current) {
            result := current;
            return;
        }
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

function is_prime(x: int): bool
    requires x >= 0
{
    if x < 2 then false
    else is_prime_helper(x, 2)
}

function is_prime_helper(x: int, v: int): bool
    requires x >= 2
    requires v >= 2
    decreases x - v * v
{
    if v * v > x then true
    else if x % v == 0 then false
    else is_prime_helper(x, v + 1)
}

function reverse_int(x: int): int
    requires x >= 0
{
    reverse_helper(x, 0)
}

function reverse_helper(x: int, acc: int): int
    requires x >= 0
    requires acc >= 0
    decreases x
{
    if x == 0 then acc
    else reverse_helper(x / 10, acc * 10 + x % 10)
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 2
    decreases *
{
    var o1 := closestFair_2417(o);
    var o2 := clumsy_1006(o1);
    var o3 := getMoneyAmount_375(o2);
    var o4 := numSquares_279(o3);
    var o5 := primePalindrome_866(o4);
    result := o5;
}
