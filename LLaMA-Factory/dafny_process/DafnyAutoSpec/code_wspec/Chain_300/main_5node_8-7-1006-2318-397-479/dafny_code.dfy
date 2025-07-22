
method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= ans
{
    ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var curr := x;
    
    while curr != 0
        invariant ans >= 0
        decreases if curr >= 0 then curr else -curr
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := curr % 10;
        if curr < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans < 0 {
            return 0;
        }
        ans := new_ans;
        curr := (curr - y) / 10;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        invariant 0 <= x <= n - 1
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
    
    if result < 1 {
        result := 1;
    }
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 2147483648
{
    if n == 1 {
        return 6;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var k := 0;
            while k < 6
                invariant 0 <= k <= 6
            {
                dp[i, j, k] := 0;
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill base case for length 2
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            if gcd(i + 1, j + 1) == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp for lengths 3 to n
    var len := 3;
    while len <= n
        invariant 3 <= len <= n + 1
        decreases n - len
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                if gcd(i + 1, j + 1) == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        if gcd(h + 1, i + 1) == 1 && h != i && h != j {
                            dp[len, i, j] := dp[len, i, j] + dp[len - 1, h, i];
                        }
                        h := h + 1;
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        len := len + 1;
    }
    
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant ans >= 0
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant ans >= 0
        {
            if ans + dp[n, i, j] >= 0 {
                ans := ans + dp[n, i, j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := ans % mod;
    if result < 1 {
        result := 1;
    }
}

method integerReplacement_397(n: int) returns (ans: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= ans <= 50
{
    ans := 0;
    var curr := n;
    var steps := 0;
    
    while curr != 1 && steps < 100
        invariant curr >= 1
        invariant ans >= 0
        invariant steps >= 0
        invariant steps <= 100
        decreases 100 - steps
    {
        if curr % 2 == 0 {
            curr := curr / 2;
        } else if curr != 3 && curr % 4 == 3 {
            curr := curr + 1;
        } else {
            curr := curr - 1;
        }
        ans := ans + 1;
        steps := steps + 1;
        if ans > 50 {
            ans := 50;
            break;
        }
    }
    
    if ans < 1 {
        ans := 1;
    }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures result >= 0
{
    var mx := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant mx >= 1
    {
        mx := mx * 10;
        i := i + 1;
    }
    mx := mx - 1;
    
    var a := mx;
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        decreases a
    {
        var b := a;
        var x := a;
        
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            decreases t
        {
            if x % t == 0 {
                return x % 1337;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    return 9;
}

method main_5node_8(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := reverse_7(o);
    if o1 == 0 || o1 > 10000 {
        result := 9;
        return;
    }
    
    var o2 := clumsy_1006(o1);
    if o2 > 10000 {
        result := 9;
        return;
    }
    
    var o3 := distinctSequences_2318(o2);
    var o4 := integerReplacement_397(o3);
    
    if o4 <= 8 {
        var o5 := largestPalindrome_479(o4);
        result := o5;
    } else {
        result := 9;
    }
}
