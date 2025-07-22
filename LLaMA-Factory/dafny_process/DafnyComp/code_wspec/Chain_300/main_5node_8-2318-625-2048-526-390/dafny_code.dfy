
function gcd_func(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd_func(b, a % b)
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

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 2147483648
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp array to 0
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
                if i != j {
                    var g1 := gcd(i + 1, j + 1);
                    if g1 == 1 {
                        var h := 0;
                        while h < 6
                            invariant 0 <= h <= 6
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
    
    result := if ans == 0 then 1 else ans;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 1000000
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var n := num;
    
    var i := 9;
    while i >= 2
        invariant 1 <= i <= 9
        invariant n >= 1
        invariant mul >= 1
        invariant ans >= 0
    {
        while n % i == 0
            invariant n >= 1
            invariant mul >= 1
            invariant ans >= 0
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if mul > 100000 || ans > 1000000 {
                result := 0;
                return;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 1000000 {
        result := ans;
    } else {
        result := 0;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 15
{
    var x := n + 1;
    
    while x <= 15
        invariant n + 1 <= x
        decreases 15 - x + 1
    {
        var y := x;
        var cnt := new int[10];
        var j := 0;
        while j < 10
            invariant 0 <= j <= 10
        {
            cnt[j] := 0;
            j := j + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            y := y / 10;
            cnt[digit] := cnt[digit] + 1;
        }
        
        var isBeautiful := true;
        var i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && cnt[i] != i {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            result := x;
            return;
        }
        
        x := x + 1;
    }
    
    result := 1;
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var count := dfs(1, n, vis);
    result := if count == 0 then 1 else count;
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    modifies vis
    ensures count >= 0
    decreases n + 1 - pos
{
    if pos == n + 1 {
        count := 1;
        return;
    }
    
    count := 0;
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant count >= 0
    {
        if !vis[j] && (j % pos == 0 || pos % j == 0) {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            count := count + subCount;
            vis[j] := false;
        }
        j := j + 1;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 1
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant a1 >= 1
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
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 1
{
    var o1 := distinctSequences_2318(o);
    var o2 := smallestFactorization_625(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    if o3 <= 15 {
        var o4 := countArrangement_526(o3);
        var o5 := lastRemaining_390(o4);
        result := o5;
    } else {
        result := 1;
    }
}
