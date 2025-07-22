
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
        var top := stk[|stk| - 1];
        stk := stk[..|stk| - 1];
        
        if k == 0 {
            stk := stk + [top * x];
        } else if k == 1 {
            stk := stk + [top / x];
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
    {
        result := result + stk[i];
        i := i + 1;
    }
    
    assume 1 <= result <= 2147483648;
}

method integerReplacement_397(n: int) returns (ans: int)
    requires 1 <= n <= 2147483648
    ensures 0 <= ans <= 50
{
    ans := 0;
    var current := n;
    
    while current != 1 && ans < 50
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 50
        decreases 50 - ans
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
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant m >= 0
        invariant m * m <= n
    {
        m := m + 1;
    }
    
    var f := new int[m + 1, n + 1];
    
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            if i == 0 && j == 0 {
                f[i, j] := 0;
            } else {
                f[i, j] := n + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
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
    if result > n || result <= 0 {
        result := 1;
    }
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures num <= result
{
    var digits: seq<int> := [];
    var temp := num;
    
    if temp == 0 {
        digits := [0];
    } else {
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
            decreases temp
        {
            digits := [temp % 10] + digits;
            temp := temp / 10;
        }
    }
    
    var n := |digits|;
    if n == 0 {
        result := num;
        return;
    }
    
    var d := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> d[k] == k
    {
        d[i] := i;
        i := i + 1;
    }
    
    i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        if i + 1 < n && digits[i] <= digits[d[i + 1]] {
            d[i] := d[i + 1];
        }
        i := i - 1;
    }
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        if i < n && d[i] < n && digits[i] < digits[d[i]] {
            var temp_digit := digits[i];
            digits := digits[i := digits[d[i]]][d[i] := temp_digit];
            break;
        }
        i := i + 1;
    }
    
    result := 0;
    i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        result := result * 10 + digits[i];
        i := i + 1;
    }
    
    if result < num {
        result := num;
    }
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
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            if result <= 1000000 - x {
                result := result + x;
            }
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
    var o3: int;
    if 1 <= o2 <= 10000 {
        o3 := numSquares_279(o2);
    } else {
        o3 := 1;
    }
    var o4 := maximumSwap_670(o3);
    var o5: int;
    if 1 <= o4 <= 1000 {
        o5 := sumOfMultiples_2652(o4);
    } else {
        o5 := 0;
    }
    result := o5;
}
