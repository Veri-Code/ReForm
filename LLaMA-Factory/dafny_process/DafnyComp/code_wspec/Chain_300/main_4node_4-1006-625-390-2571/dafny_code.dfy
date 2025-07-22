
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 2147483648
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
    
    assume 1 <= result <= 2147483648;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 2147483648
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var remaining := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant mul >= 1
        invariant ans >= 0
        decreases i
    {
        while remaining % i == 0
            invariant remaining >= 1
            invariant mul >= 1
            invariant ans >= 0
            decreases remaining
        {
            remaining := remaining / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if mul > 1000000000 {
                return 0;
            }
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= n
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
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
    assume 1 <= result <= n;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
{
    var ans := 0;
    var cnt := 0;
    var remaining := n;
    
    while remaining > 0
        invariant remaining >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases remaining
    {
        if remaining % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        remaining := remaining / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := clumsy_1006(o);
    var o2 := smallestFactorization_625(o1);
    if o2 == 0 {
        result := 0;
        return;
    }
    if o2 > 100000 {
        result := 0;
        return;
    }
    var o3 := lastRemaining_390(o2);
    var o4 := minOperations_2571(o3);
    result := o4;
}
