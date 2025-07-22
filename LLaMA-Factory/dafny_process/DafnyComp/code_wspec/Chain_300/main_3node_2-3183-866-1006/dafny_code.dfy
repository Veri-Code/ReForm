
method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 1000000007
{
    var mod := 1000000007;
    var f := new int[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant f.Length == n + 1
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant f.Length == n + 1
        invariant f[0] == 1
        invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    if n >= 2 {
        j := 2;
        while j <= n
            invariant 2 <= j <= n + 1
            invariant f.Length == n + 1
            invariant forall k :: 0 <= k < f.Length ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 2]) % mod;
            j := j + 1;
        }
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant f.Length == n + 1
            invariant forall k :: 0 <= k < f.Length ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    result := ans;
    assert 0 <= result < mod;
    if result == 0 {
        result := 1;
    }
}

method isPrime(x: int) returns (result: bool)
    requires x >= 1
{
    if x < 2 {
        return false;
    }
    if x == 2 {
        return true;
    }
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method reverse(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    var res := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
    result := res;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 100000000
    ensures result >= n
{
    var current := n;
    while current <= 100000000
        invariant current >= n
        invariant current >= 1
        decreases 100000000 - current + 1
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                return current;
            }
        }
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    result := 100000000;
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stk := new int[4 * n]; // Upper bound on stack size
    var stkSize := 0;
    
    // Push initial value
    stk[0] := n;
    stkSize := 1;
    
    var x := n - 1;
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 1 <= stkSize <= stk.Length
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            // Multiplication
            if stkSize > 0 {
                var top := stk[stkSize - 1];
                stk[stkSize - 1] := top * x;
            }
        } else if k == 1 {
            // Division
            if stkSize > 0 {
                var top := stk[stkSize - 1];
                stk[stkSize - 1] := top / x;
            }
        } else if k == 2 {
            // Addition (push positive)
            if stkSize < stk.Length {
                stk[stkSize] := x;
                stkSize := stkSize + 1;
            }
        } else {
            // Subtraction (push negative)
            if stkSize < stk.Length {
                stk[stkSize] := -x;
                stkSize := stkSize + 1;
            }
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum the stack
    var sum := 0;
    var i := 0;
    while i < stkSize
        invariant 0 <= i <= stkSize
    {
        sum := sum + stk[i];
        i := i + 1;
    }
    
    result := sum;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000
    ensures true
{
    var o1 := numberOfWays_3183(o);
    var o2: int;
    if o1 <= 100000000 {
        o2 := primePalindrome_866(o1);
    } else {
        o2 := 100000000;
    }
    var o3: int;
    if o2 <= 10000 {
        o3 := clumsy_1006(o2);
    } else {
        o3 := 0;
    }
    result := o3;
}
