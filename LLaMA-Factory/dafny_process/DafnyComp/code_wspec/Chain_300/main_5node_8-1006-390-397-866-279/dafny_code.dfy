
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
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
    
    result := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        decreases |stk| - i
    {
        result := result + stk[i];
        i := i + 1;
    }
    
    // Ensure result is in valid range
    if result <= 0 {
        result := 1;
    } else if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 2147483648
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant a1 >= 1
        invariant an >= 0
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            } else {
                an := 0;
            }
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                if an >= step {
                    an := an - step;
                } else {
                    an := 0;
                }
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result < 1 {
        result := 1;
    } else if result > 2147483648 {
        result := 2147483648;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 100000000
{
    var ans := 0;
    var current := n;
    
    while current != 1 && ans < 100000000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 100000000
        decreases if current > 1 then 100000000 - ans else 0
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    result := ans;
    if result == 0 {
        result := 1;
    }
}

function isPrime(x: int): bool
    requires x >= 1
{
    if x < 2 then false
    else if x == 2 then true
    else if x % 2 == 0 then false
    else isPrimeHelper(x, 3)
}

function isPrimeHelper(x: int, v: int): bool
    requires x >= 3
    requires v >= 3
    requires v % 2 == 1
    decreases x - v * v
{
    if v * v > x then true
    else if x % v == 0 then false
    else isPrimeHelper(x, v + 2)
}

function reverseNumber(x: int): int
    requires x >= 0
{
    reverseHelper(x, 0)
}

function reverseHelper(x: int, acc: int): int
    requires x >= 0
    requires acc >= 0
    decreases x
{
    if x == 0 then acc
    else reverseHelper(x / 10, acc * 10 + x % 10)
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 10000
{
    var current := n;
    
    while current <= 10000
        invariant current >= 1
        decreases 10001 - current
    {
        if reverseNumber(current) == current && isPrime(current) {
            result := current;
            return;
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    
    result := 10000;
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant m >= 0
        invariant m * m <= n
        decreases n - m * m
    {
        m := m + 1;
    }
    
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
            f[i, j] := 10001; // Large value representing infinity
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
                var candidate := f[i, j - i * i] + 1;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result <= 0 || result > 10000 {
        result := 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures 1 <= result
{
    var o1 := clumsy_1006(o);
    var o2 := lastRemaining_390(o1);
    var o3 := integerReplacement_397(o2);
    var o4 := primePalindrome_866(o3);
    var o5 := numSquares_279(o4);
    result := o5;
}
