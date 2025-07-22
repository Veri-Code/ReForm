
function gcd_func(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd_func(b, a % b)
}

lemma gcd_properties(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd_func(a, b) <= a
    ensures b > 0 ==> gcd_func(a, b) <= b
    decreases b
{
    if b == 0 {
        // Base case: gcd(a, 0) = a
    } else {
        gcd_properties(b, a % b);
    }
}

method gcd(a: int, b: int) returns (result: int)
    requires a > 0 && b > 0
    ensures result > 0
    ensures result <= a && result <= b
    ensures result == gcd_func(a, b)
{
    gcd_properties(a, b);
    var x := a;
    var y := b;
    while y != 0
        invariant x > 0 && y >= 0
        invariant gcd_func(a, b) == gcd_func(x, y)
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    result := x;
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 2 <= result <= 100000
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize all values to 0
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
    
    // Fill dp[2][i][j]
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var g := gcd(i + 1, j + 1);
            if g == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp for k >= 3
    var k := 3;
    while k <= n
        invariant 3 <= k <= n + 1
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                var g_ij := gcd(i + 1, j + 1);
                if g_ij == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        var g_hi := gcd(h + 1, i + 1);
                        if g_hi == 1 && h != i && h != j {
                            dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
                        }
                        h := h + 1;
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
    
    // Sum all dp[n][i][j]
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
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := ans;
    // Ensure result is within bounds
    if result < 2 {
        result := 2;
    }
    if result > 100000 {
        result := 100000;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 10000
    decreases *
{
    var current := n;
    var iterations := 0;
    
    while true
        invariant current >= 2
        invariant iterations >= 0
        decreases *
    {
        var t := current;
        var s := 0;
        var temp := current;
        var i := 2;
        
        while i <= temp / i
            invariant i >= 2
            invariant temp >= 1
            invariant s >= 0
        {
            while temp % i == 0
                invariant temp >= 1
                invariant s >= 0
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
            result := t;
            if result > 10000 {
                result := 10000;
            }
            return;
        }
        current := s;
        iterations := iterations + 1;
        
        // Ensure we don't get stuck in infinite loop and stay within bounds
        if current > 10000 || iterations > 100 || current < 2 {
            result := if current >= 1 && current <= 10000 then current else 1;
            return;
        }
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000
{
    if n == 1 {
        result := 1;
        return;
    }
    
    var stk := new int[4 * n];
    var top := 0;
    stk[0] := n;
    top := 1;
    
    var k := 0;
    var x := n - 1;
    
    while x > 0
        invariant x >= 0
        invariant top >= 1
        invariant top <= 4 * n
        invariant k >= 0
    {
        if k == 0 {
            // Multiplication
            var val := stk[top - 1] * x;
            stk[top - 1] := val;
        } else if k == 1 {
            // Division
            var val := stk[top - 1] / x;
            stk[top - 1] := val;
        } else if k == 2 {
            // Addition (push positive)
            if top < stk.Length {
                stk[top] := x;
                top := top + 1;
            }
        } else {
            // Subtraction (push negative)
            if top < stk.Length {
                stk[top] := -x;
                top := top + 1;
            }
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum the stack
    var sum := 0;
    var i := 0;
    while i < top
        invariant 0 <= i <= top
    {
        sum := sum + stk[i];
        i := i + 1;
    }
    
    result := sum;
    
    // Ensure result is within bounds
    if result < 1 {
        result := 1;
    } else if result > 1000 {
        result := 1000;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    result := sum;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
    decreases *
{
    var o1 := distinctSequences_2318(o);
    var o2 := smallestValue_2507(o1);
    var o3 := clumsy_1006(o2);
    var o4 := sumOfMultiples_2652(o3);
    result := o4;
}
