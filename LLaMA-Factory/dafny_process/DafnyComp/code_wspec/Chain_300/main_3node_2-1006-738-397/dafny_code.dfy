
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 1000000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        invariant forall i :: 0 <= i < |stk| ==> stk[i] >= -100000 && stk[i] <= 100000000
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            if top > 0 && x > 0 && top <= 100000000 / x {
                stk := stk[..|stk| - 1] + [top * x];
            } else if top <= 0 {
                var product := top * x;
                if product >= -100000 {
                    stk := stk[..|stk| - 1] + [product];
                } else {
                    stk := stk[..|stk| - 1] + [-100000];
                }
            } else {
                stk := stk[..|stk| - 1] + [100000000];
            }
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
        invariant 0 <= result <= 1000000000
        decreases |stk| - i
    {
        var newResult := result + stk[i];
        if newResult >= 0 && newResult <= 1000000000 {
            result := newResult;
        } else if newResult > 1000000000 {
            result := 1000000000;
        } else {
            result := 0;
        }
        i := i + 1;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 2147483648
{
    if n == 0 {
        result := 1;
        return;
    }
    
    var s := [];
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant |s| <= 10
        decreases temp
    {
        var digit := temp % 10;
        s := [digit] + s;
        temp := temp / 10;
        if |s| >= 10 {
            break;
        }
    }
    
    if |s| == 0 {
        result := 1;
        return;
    }
    
    var i := 1;
    while i < |s| && s[i-1] <= s[i]
        invariant 1 <= i <= |s|
        decreases |s| - i
    {
        i := i + 1;
    }
    
    if i < |s| {
        while i > 0 && s[i-1] > s[i]
            invariant 0 <= i < |s|
            invariant |s| >= 1
            decreases i
        {
            if s[i-1] > 0 {
                s := s[i-1 := s[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        while i < |s|
            invariant 0 <= i <= |s|
            decreases |s| - i
        {
            s := s[i := 9];
            i := i + 1;
        }
    }
    
    result := 1;
    i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 1
        decreases |s| - i
    {
        if result <= 214748364 {
            var newResult := result * 10 + s[i];
            if newResult <= 2147483648 && newResult >= 1 {
                result := newResult;
            } else if newResult > 2147483648 {
                result := 2147483648;
                break;
            } else {
                result := 1;
            }
        } else {
            result := 2147483648;
            break;
        }
        i := i + 1;
    }
    
    if result < 1 {
        result := 1;
    }
    if result > 2147483648 {
        result := 2147483648;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= 0
{
    var current := n;
    result := 0;
    
    while current != 1 && result < 100
        invariant current >= 1
        invariant result >= 0
        invariant result <= 100
        decreases 100 - result
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            if current < 2147483647 {
                current := current + 1;
            } else {
                current := current - 1;
            }
        } else {
            current := current - 1;
        }
        result := result + 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := clumsy_1006(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    var o3 := integerReplacement_397(o2);
    result := o3;
}
