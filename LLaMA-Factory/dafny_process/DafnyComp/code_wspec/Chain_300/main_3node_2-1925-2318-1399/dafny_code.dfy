
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures ans >= 0
{
    ans := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
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
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    result := 1;
    while result * result < x
        invariant result >= 1
        invariant (result - 1) * (result - 1) <= x
        decreases x - result * result
    {
        result := result + 1;
    }
    
    if result * result > x {
        result := result - 1;
    }
}

function gcd_spec(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd_spec(b, a % b)
}

lemma gcd_divides(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd_spec(a, b) > 0
    ensures a % gcd_spec(a, b) == 0 && (b == 0 || b % gcd_spec(a, b) == 0)
    decreases b
{
    if b == 0 {
    } else {
        gcd_divides(b, a % b);
    }
}

lemma gcd_positive(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd_spec(a, b) > 0
    decreases b
{
    if b == 0 {
    } else {
        gcd_positive(b, a % b);
    }
}

method gcd(a: int, b: int) returns (result: int)
    requires a > 0 && b > 0
    ensures result > 0
    ensures a % result == 0 && b % result == 0
{
    var x, y := a, b;
    while y != 0
        invariant x > 0 && y >= 0
        invariant gcd_spec(a, b) == gcd_spec(x, y)
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    result := x;
    gcd_positive(a, b);
    gcd_divides(a, b);
}

method distinctSequences_2318(n: int) returns (ans: int)
    requires 1 <= n <= 10000
    ensures ans >= 1
{
    if n == 1 {
        return 6;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize all dp values to 0
    var k := 0;
    while k <= n
        invariant 0 <= k <= n + 1
    {
        var i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                dp[k, i, j] := 0;
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
    
    // Initialize dp for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            if i != j {
                var g := gcd(i + 1, j + 1);
                if g == 1 {
                    dp[2, i, j] := 1;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp for lengths 3 to n
    k := 3;
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
                if i != j {
                    var g1 := gcd(i + 1, j + 1);
                    if g1 == 1 {
                        dp[k, i, j] := 0;
                        var h := 0;
                        while h < 6
                            invariant 0 <= h <= 6
                            invariant dp[k, i, j] >= 0
                        {
                            if h != i && h != j {
                                var g2 := gcd(h + 1, i + 1);
                                if g2 == 1 {
                                    dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
                                }
                            }
                            h := h + 1;
                        }
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
    
    // Sum all possibilities for length n
    ans := 0;
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
    
    if ans == 0 {
        ans := 1;
    }
}

method digitSum(num: int) returns (sum: int)
    requires num >= 1
    ensures sum >= 1
{
    sum := 0;
    var n := num;
    while n > 0
        invariant n >= 0
        invariant sum >= 0
        decreases n
    {
        sum := sum + (n % 10);
        n := n / 10;
    }
    if sum == 0 {
        sum := 1;
    }
}

method countLargestGroup_1399(n: int) returns (ans: int)
    requires 1 <= n <= 10000
    ensures ans >= 1
{
    var cnt := new int[46];
    var i := 0;
    while i < 46
        invariant 0 <= i <= 46
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
    {
        var s := digitSum(i);
        if s < 46 {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
            }
        }
        i := i + 1;
    }
    
    ans := 0;
    i := 0;
    while i < 46
        invariant 0 <= i <= 46
        invariant ans >= 0
    {
        if cnt[i] == mx {
            ans := ans + 1;
        }
        i := i + 1;
    }
    
    if ans == 0 {
        ans := 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures result >= 1
{
    var o1 := countTriples_1925(o);
    assume {:axiom} 1 <= o1 <= 10000;
    var o2 := distinctSequences_2318(o1);
    assume {:axiom} 1 <= o2 <= 10000;
    result := countLargestGroup_1399(o2);
}
