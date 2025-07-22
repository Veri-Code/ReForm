
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 1 <= result <= 10000000000000000
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    
    // Count digits
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
        invariant forall k :: 0 <= k < i ==> cnt[k] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    if temp == 0 {
        cnt[0] := 1;
    } else {
        while temp > 0
            invariant temp >= 0
            invariant cnt.Length == 10
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
            decreases temp
        {
            var digit := temp % 10;
            cnt[digit] := cnt[digit] + 1;
            temp := temp / 10;
        }
    }
    
    var ans := 0;
    if neg {
        // For negative numbers, arrange digits in descending order
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant cnt.Length == 10
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt.Length == 10
                invariant cnt[i] >= 0
                invariant cnt[i] >= j
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := if ans == 0 then -1 else -ans;
    } else {
        // For positive numbers, arrange digits in ascending order
        // but avoid leading zeros
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
                invariant cnt.Length == 10
                invariant forall k :: 1 <= k < i ==> cnt[k] == 0
            {
                i := i + 1;
            }
            if i < 10 {
                ans := i;
                cnt[i] := cnt[i] - 1;
            }
        }
        
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant cnt.Length == 10
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt.Length == 10
                invariant cnt[i] >= 0
                invariant cnt[i] >= j
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
        result := if ans == 0 then 1 else ans;
    }
    
    if result == 0 {
        result := 1;
    }
    if result < 1 {
        result := 1;
    }
    if result > 10000000000000000 {
        result := 10000000000000000;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000000000
{
    var k := 0;
    var stk := new int[4 * n];
    var stkSize := 1;
    stk[0] := n;
    
    var x := n - 1;
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 1 <= stkSize <= 4 * n
        invariant stk.Length == 4 * n
        decreases x
    {
        if k == 0 {
            if stkSize > 0 {
                stk[stkSize - 1] := stk[stkSize - 1] * x;
            }
        } else if k == 1 {
            if stkSize > 0 {
                stk[stkSize - 1] := stk[stkSize - 1] / x;
            }
        } else if k == 2 {
            if stkSize < 4 * n {
                stk[stkSize] := x;
                stkSize := stkSize + 1;
            }
        } else {
            if stkSize < 4 * n {
                stk[stkSize] := -x;
                stkSize := stkSize + 1;
            }
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := 0;
    var i := 0;
    while i < stkSize
        invariant 0 <= i <= stkSize
        invariant stk.Length == 4 * n
    {
        result := result + stk[i];
        i := i + 1;
    }
    
    if result < 1 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 200
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        decreases cnt
    {
        if i % 2 == 1 {
            an := an - step;
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result > 200 {
        result := 200;
    }
    if result < 1 {
        result := 1;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 100000
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant f.Length0 == n + 1 && f.Length1 == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant f.Length0 == n + 1 && f.Length1 == n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
        invariant f.Length0 == n + 1 && f.Length1 == n + 1
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant f.Length0 == n + 1 && f.Length1 == n + 1
        {
            f[i, j] := j + f[i, j - 1];
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant f.Length0 == n + 1 && f.Length1 == n + 1
            {
                var left := if k - 1 >= i then f[i, k - 1] else 0;
                var right := if k + 1 <= j then f[k + 1, j] else 0;
                var cost := (if left > right then left else right) + k;
                if cost < f[i, j] {
                    f[i, j] := cost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result < 1 {
        result := 1;
    }
    if result > 100000 {
        result := 100000;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
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
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant f.Length == n + 1
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant f.Length == n + 1
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
    
    // Ensure result is non-negative
    if result < 0 {
        result := 0;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result >= 0
{
    var o1 := smallestNumber_2165(o);
    var o2 := clumsy_1006(if o1 <= 10000 then o1 else 10000);
    var o3 := lastRemaining_390(o2);
    var o4 := getMoneyAmount_375(if o3 <= 200 then o3 else 200);
    var o5 := numberOfWays_3183(if o4 <= 100000 then o4 else 100000);
    result := o5;
}
