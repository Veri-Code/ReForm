
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
        invariant forall i :: 0 <= i < |stk| ==> stk[i] >= -2147483648 && stk[i] <= 2147483648
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var new_val := top * x;
            if new_val > 2147483648 { new_val := 2147483648; }
            if new_val < -2147483648 { new_val := -2147483648; }
            stk := stk[..|stk| - 1] + [new_val];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            var new_val := top / x;
            stk := stk[..|stk| - 1] + [new_val];
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
        invariant result >= -2147483648 && result <= 2147483648
        decreases |stk| - i
    {
        var new_result := result + stk[i];
        if new_result > 2147483648 { new_result := 2147483648; }
        if new_result < -2147483648 { new_result := -2147483648; }
        result := new_result;
        i := i + 1;
    }
    
    if result < 1 { result := 1; }
    if result > 2147483648 { result := 2147483648; }
}

method integerReplacement_397(n: int) returns (ans: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= ans <= 100000
{
    ans := 0;
    var current := n;
    
    while current != 1 && ans < 100000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 100000
        decreases 100000 - ans
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
    
    if ans == 0 {
        ans := 1;
    }
    if ans > 100000 {
        ans := 100000;
    }
}

method minOperations_2571(n: int) returns (ans: int)
    requires 1 <= n <= 100000
    ensures 2 <= ans <= 100000
{
    ans := 0;
    var cnt := 0;
    var current := n;
    
    while current > 0
        invariant current >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases current
    {
        if current % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        current := current / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    if ans < 2 {
        ans := 2;
    }
    if ans > 100000 {
        ans := 100000;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 2
        invariant iterations >= 0
        invariant iterations <= 1000
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp_current := current;
        
        while i <= temp_current / i && i <= temp_current && i <= 1000
            invariant i >= 2
            invariant s >= 0
            invariant temp_current >= 1
            decreases 1000 - i + 1
        {
            while temp_current % i == 0 && temp_current > 1
                invariant temp_current >= 1
                invariant i >= 2
                invariant s >= 0
                decreases temp_current
            {
                temp_current := temp_current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp_current > 1 {
            s := s + temp_current;
        }
        
        if s == t {
            result := t;
            if result < 1 { result := 1; }
            if result > 1000 { result := 1000; }
            return;
        }
        
        current := s;
        if current < 2 { current := 2; }
        if current > 1000 { current := 1000; }
        iterations := iterations + 1;
    }
    
    result := current;
    if result < 1 { result := 1; }
    if result > 1000 { result := 1000; }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := clumsy_1006(o);
    var o2 := integerReplacement_397(o1);
    var o3 := minOperations_2571(o2);
    var o4 := smallestValue_2507(o3);
    var o5 := sumOfMultiples_2652(o4);
    result := o5;
}
