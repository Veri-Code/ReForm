
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

method sqrt_int(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    result := 1;
    while (result + 1) * (result + 1) <= x
        invariant result >= 0
        invariant result * result <= x
        decreases x - result * result
    {
        result := result + 1;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 250
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant 1 <= current
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i <= temp / i && i <= 100000
            invariant i >= 2
            invariant s >= 0
            invariant temp >= 1
        {
            while temp % i == 0 && temp > 1
                invariant temp >= 1
                invariant i >= 2
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
            result := t;
            if result < 1 { result := 1; }
            if result > 250 { result := 250; }
            return;
        }
        
        current := s;
        if current < 1 { current := 1; }
        iterations := iterations + 1;
    }
    
    result := 1;
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 1000000000
{
    result := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant result >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant result >= 0
        {
            var x := a * a + b * b;
            var c := sqrt_int(x);
            
            if c <= n && c * c == x {
                result := result + 1;
            }
            
            b := b + 1;
        }
        a := a + 1;
    }
    
    if result == 0 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 10000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant a1 >= 1
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 && an >= step {
                an := an - step;
            }
        }
        
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result > 10000 {
        result := 10000;
    }
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 15
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
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
    if result == 0 {
        result := 1;
    }
    if result > 15 {
        result := 15;
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
    
    result := dfs_helper(1, n, vis);
}

method dfs_helper(pos: int, n: int, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    ensures count >= 0
    modifies vis
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

method main_5node_8(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures 0 <= result
{
    var o1 := smallestValue_2507(o);
    var o2 := countTriples_1925(o1);
    var o3 := lastRemaining_390(o2);
    var o4 := distinctSequences_2318(o3);
    var o5 := countArrangement_526(o4);
    result := o5;
}
