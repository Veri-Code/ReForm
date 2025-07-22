
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
        invariant forall i :: 0 <= i < |stk| ==> -1000000000 <= stk[i] <= 1000000000
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var new_val := top * x;
            if new_val > 1000000000 {
                new_val := 1000000000;
            } else if new_val < -1000000000 {
                new_val := -1000000000;
            }
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
        invariant -10000000000 <= result <= 10000000000
        decreases |stk| - i
    {
        var new_result := result + stk[i];
        if new_result > 10000000000 {
            result := 10000000000;
        } else if new_result < -10000000000 {
            result := -10000000000;
        } else {
            result := new_result;
        }
        i := i + 1;
    }
    
    if result < 1 {
        result := 1;
    } else if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant 1 <= a1 <= 1000000000
        invariant 0 <= an <= 1000000000
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            } else {
                an := 0;
            }
            if cnt % 2 == 1 && a1 + step <= 1000000000 {
                a1 := a1 + step;
            }
        } else {
            if a1 + step <= 1000000000 {
                a1 := a1 + step;
            }
            if cnt % 2 == 1 && an >= step {
                an := an - step;
            } else if cnt % 2 == 1 {
                an := 0;
            }
        }
        cnt := cnt / 2;
        if step <= 500000000 {
            step := step * 2;
        }
        i := i + 1;
    }
    result := a1;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 2 <= result <= 100000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 100
        invariant 2 <= current <= 1000000
        invariant 0 <= iterations <= 100
        decreases 100 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i <= temp / i
            invariant 2 <= i
            invariant s >= 0
            invariant temp >= 1
            decreases temp - i * i + 1
        {
            while temp % i == 0
                invariant temp >= 1
                invariant i >= 2
                decreases temp
            {
                temp := temp / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            result := if t >= 2 && t <= 100000 then t else 2;
            return;
        }
        current := if s >= 2 && s <= 100000 then s else 2;
        iterations := iterations + 1;
    }
    
    result := if current >= 2 && current <= 100000 then current else 2;
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483647
    ensures 0 <= result <= 2147483647
{
    var ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var current := x;
    
    while current != 0
        invariant -2147483648 <= ans <= 2147483647
        invariant -2147483648 <= current <= 2147483647
        decreases if current >= 0 then current else -current
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            result := 0;
            return;
        }
        
        var y := current % 10;
        if current < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans < -2147483648 || new_ans > 2147483647 {
            result := 0;
            return;
        }
        ans := new_ans;
        current := (current - y) / 10;
    }
    
    result := if ans >= 0 then ans else 0;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483647
    ensures 0 <= result <= 2147483647
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var current := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant current >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while current % i == 0
            invariant current >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases current
        {
            current := current / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if current < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures 0 <= result <= 2147483647
{
    var o1 := clumsy_1006(o);
    var o2 := lastRemaining_390(o1);
    var o3 := smallestValue_2507(if o2 >= 2 && o2 <= 100000 then o2 else 2);
    var o4 := reverse_7(o3);
    var o5 := smallestFactorization_625(if o4 >= 1 then o4 else 1);
    result := o5;
}
