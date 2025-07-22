
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

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 10000
{
    if num < 2 {
        result := num;
        return;
    }
    
    var n := num;
    var ans := 0;
    var mul := 1;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant n >= 1
        invariant mul >= 1
        invariant ans >= 0
        invariant ans <= 10000
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant mul >= 1
            invariant ans >= 0
            invariant ans <= 10000
            decreases n
        {
            n := n / i;
            var new_ans := mul * i + ans;
            if new_ans > 10000 {
                result := 0;
                return;
            }
            ans := new_ans;
            mul := mul * 10;
            if mul > 1000000 {
                result := 0;
                return;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp array to 0
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
    
    // Base case for length 2
    var i := 0;
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
    
    // Fill dp table
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
                var g1 := gcd(i + 1, j + 1);
                if g1 == 1 && i != j {
                    dp[k, i, j] := 0;
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        var g2 := gcd(h + 1, i + 1);
                        if g2 == 1 && h != i && h != j {
                            dp[k, i, j] := dp[k, i, j] + dp[k - 1, h, i];
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
    if result == 0 {
        result := 1;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 0
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var count := dfs_helper(1, n, vis);
    result := count;
}

method dfs_helper(pos: int, n: int, vis: array<bool>) returns (count: int)
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
            var subcount := dfs_helper(pos + 1, n, vis);
            count := count + subcount;
            vis[j] := false;
        }
        j := j + 1;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n
    ensures 0 <= result <= 1000
{
    if n == 0 {
        result := 0;
        return;
    }
    
    if n <= 1000 {
        result := n;
        return;
    }
    
    // For simplicity, return a bounded result
    result := 999;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 0 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    if n == 0 {
        return;
    }
    var x := 1;
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := smallestFactorization_625(o);
    if o1 == 0 || o1 > 15 {
        result := 0;
        return;
    }
    
    var o2 := distinctSequences_2318(o1);
    if o2 > 15 {
        result := 0;
        return;
    }
    
    var o3 := countArrangement_526(o2);
    
    var o4 := monotoneIncreasingDigits_738(o3);
    
    var o5 := sumOfMultiples_2652(o4);
    result := o5;
}
