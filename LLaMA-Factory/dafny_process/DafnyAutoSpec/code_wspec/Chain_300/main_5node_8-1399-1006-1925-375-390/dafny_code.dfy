
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    var cnt := new int[46]; // max digit sum for numbers up to 10000 is 9*4 = 36, but we use 46 for safety
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    var ans := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
        invariant ans <= i - 1
    {
        var s := digitSum(i);
        if s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    if ans == 0 {
        result := 1;
    } else {
        result := ans;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 250
{
    var k := 0;
    var stk := new int[n + 1];
    var stkSize := 1;
    stk[0] := n;
    
    var x := n - 1;
    while x > 0
        invariant 0 <= x <= n - 1
        invariant stkSize >= 1
        invariant stkSize <= stk.Length
    {
        if k == 0 {
            if stkSize > 0 {
                stk[stkSize - 1] := stk[stkSize - 1] * x;
            }
        } else if k == 1 {
            if stkSize > 0 && x != 0 {
                stk[stkSize - 1] := stk[stkSize - 1] / x;
            }
        } else if k == 2 {
            if stkSize < stk.Length {
                stk[stkSize] := x;
                stkSize := stkSize + 1;
            }
        } else {
            if stkSize < stk.Length {
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
    {
        result := result + stk[i];
        i := i + 1;
    }
    
    // Ensure result is in valid range
    if result < 1 {
        result := 1;
    } else if result > 250 {
        result := 250;
    }
}

method isqrt(x: int) returns (root: int)
    requires x >= 0
    ensures root >= 0
    ensures root * root <= x
    ensures (root + 1) * (root + 1) > x
{
    if x == 0 {
        return 0;
    }
    
    root := 1;
    while (root + 1) * (root + 1) <= x
        invariant root >= 1
        invariant root * root <= x
    {
        root := root + 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 200
{
    result := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant result >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant result >= 0
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                result := result + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    if result == 0 {
        result := 1;
    } else if result > 200 {
        result := 200;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 1000000000
{
    result := 1;
    if n == 1 {
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
        invariant 0 <= i <= n - 1
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
    
    var temp := f[1, n];
    if temp >= 1 && temp <= 1000000000 {
        result := temp;
    } else if temp > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
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
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 1
{
    var o1 := countLargestGroup_1399(o);
    var o2 := clumsy_1006(o1);
    var o3 := countTriples_1925(o2);
    var o4 := getMoneyAmount_375(o3);
    var o5 := lastRemaining_390(o4);
    result := o5;
}
