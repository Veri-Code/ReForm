
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 250
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 < a <= mx
        invariant mx == power10(n) - 1
        decreases a
    {
        // Create palindrome by mirroring a
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
        
        // Check if x can be expressed as product of two n-digit numbers
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            invariant t <= mx
            decreases t
        {
            if x % t == 0 {
                var quotient := x / t;
                if quotient <= mx && quotient > mx / 10 {
                    var mod_result := x % 1337;
                    if mod_result == 0 {
                        return 1337 % 1337;
                    }
                    assert 1 <= mod_result <= 1336;
                    if mod_result <= 250 {
                        return mod_result;
                    } else {
                        return 250;
                    }
                }
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 10000
{
    var ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
        decreases n - a
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
            decreases n - b
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    if ans == 0 {
        return 1; // Ensure postcondition
    }
    if ans > 10000 {
        return 10000;
    }
    return ans;
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 0
{
    if n == 1 {
        return 6;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
        decreases 6 - i
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            decreases 6 - j
        {
            if gcd(i + 1, j + 1) == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp for lengths 3 to n
    var k := 3;
    while k <= n
        invariant 3 <= k <= n + 1
        decreases n + 1 - k
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
            decreases 6 - i
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
                decreases 6 - j
            {
                if gcd(i + 1, j + 1) == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                        decreases 6 - h
                    {
                        if gcd(h + 1, i + 1) == 1 && h != i && h != j {
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
    
    // Sum all possibilities for length n
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant ans >= 0
        decreases 6 - i
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant ans >= 0
            decreases 6 - j
        {
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    
    return ans;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := countTriples_1925(o1);
    var o3 := distinctSequences_2318(o2);
    result := o3;
}

// Helper functions
function power10(n: int): int
    requires n >= 0
    ensures power10(n) > 0
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures (isqrt(x) + 1) * (isqrt(x) + 1) > x
{
    if x == 0 then 0
    else if x < 4 then 1
    else
        var guess := isqrt(x / 4) * 2;
        if (guess + 1) * (guess + 1) <= x then guess + 1
        else guess
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures gcd(a, b) <= a && gcd(a, b) <= b
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}
