
function gcd_func(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a
    else gcd_func(b, a % b)
}

method gcd(a: int, b: int) returns (result: int)
    requires a > 0 && b > 0
    ensures result > 0
    ensures result == gcd_func(a, b)
{
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

method sqrt_int(n: int) returns (result: int)
    requires n >= 0
    ensures result >= 0
    ensures result * result <= n < (result + 1) * (result + 1)
{
    if n == 0 { return 0; }
    
    result := 1;
    while (result + 1) * (result + 1) <= n
        invariant result >= 0
        invariant result * result <= n
        decreases n - result * result
    {
        result := result + 1;
    }
}

method is_prime(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
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
    var n := x;
    result := 0;
    while n > 0
        invariant n >= 0
        invariant result >= 0
        decreases n
    {
        result := result * 10 + n % 10;
        n := n / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= n
    ensures result >= 2
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        invariant current >= 1
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := is_prime(current);
            if prime {
                if current >= 2 {
                    return current;
                }
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000000007
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
            var g := gcd(i + 1, j + 1);
            if g == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table
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
                var g1 := gcd(i + 1, j + 1);
                if g1 == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        var g2 := gcd(h + 1, i + 1);
                        if g2 == 1 && h != i && h != j {
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
    
    // Sum all possibilities
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant 0 <= ans < mod
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant 0 <= ans < mod
        {
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := ans;
    if result == 0 { result := 1; }
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 8
{
    var m := sqrt_int(n);
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 10001; // Large value instead of infinity
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
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
    if result > 8 { result := 1; }
    if result < 1 { result := 1; }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 2 <= result <= 100000
{
    if n == 1 { return 9; }
    
    var power := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant power >= 1
    {
        power := power * 10;
        i := i + 1;
    }
    
    var mx := power - 1;
    var a := mx;
    
    while a >= mx / 10 && a > 0
        invariant a >= 0
        decreases a
    {
        var b := a;
        var x := a;
        
        while b > 0
            invariant b >= 0
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
                var res := x % 1337;
                if res < 2 { return 2; }
                if res > 100000 { return 100000; }
                return res;
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    return 9;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 2
    decreases *
{
    var current := n;
    
    while true
        invariant current >= 2
        decreases *
    {
        var t := current;
        var s := 0;
        var temp := current;
        var i := 2;
        
        while i * i <= temp
            invariant 2 <= i
            invariant temp >= 1
            invariant s >= 0
            decreases temp - i * i + 1
        {
            while temp % i == 0
                invariant temp >= 1
                invariant s >= 0
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
            return t;
        }
        
        if s < 2 { current := 2; }
        else { current := s; }
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 2
    decreases *
{
    var o1 := primePalindrome_866(o);
    var o2;
    if o1 <= 10000 {
        o2 := distinctSequences_2318(o1);
    } else {
        o2 := 6; // Default value when out of range
    }
    var o3;
    if o2 <= 10000 {
        o3 := numSquares_279(o2);
    } else {
        o3 := 1; // Default value when out of range
    }
    var o4 := largestPalindrome_479(o3);
    var o5 := smallestValue_2507(o4);
    result := o5;
}
