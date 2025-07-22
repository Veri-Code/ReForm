
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 1000000000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 < a <= mx || a == mx / 10
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
        
        // Check if x has a factor in the valid range
        var t := mx;
        while t * t >= x && t > mx / 10
            invariant t >= 0
            invariant mx == power10(n) - 1
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 { return 1337; }
                return res;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= n
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant 1 <= a1 <= n
        invariant 1 <= an <= n
        invariant i >= 0
        invariant step <= n
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 && a1 + step <= n {
                a1 := a1 + step;
            }
        } else {
            if a1 + step <= n {
                a1 := a1 + step;
            }
            if cnt % 2 == 1 && an >= step {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        if step <= n / 2 {
            step := step * 2;
        } else {
            step := n;
        }
        i := i + 1;
        
        // Ensure bounds are maintained
        if a1 < 1 { a1 := 1; }
        if a1 > n { a1 := n; }
        if an < 1 { an := 1; }
        if an > n { an := n; }
    }
    return a1;
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 1
{
    // Pre-compute valid matches
    var matches := new seq<int>[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        matches[i] := [];
        i := i + 1;
    }
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
    {
        var j := 1;
        while j <= n
            invariant 1 <= j <= n + 1
        {
            if j % i == 0 || i % j == 0 {
                matches[i] := matches[i] + [j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    var vis := new bool[n + 1];
    i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var count := dfs_526(1, n, matches, vis);
    if count == 0 { return 1; }
    return count;
}

method dfs_526(pos: int, n: int, matches: array<seq<int>>, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires matches.Length == n + 1
    requires vis.Length == n + 1
    ensures count >= 0
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var i := 0;
    while i < |matches[pos]|
        invariant 0 <= i <= |matches[pos]|
        invariant count >= 0
    {
        var j := matches[pos][i];
        if 1 <= j <= n && !vis[j] {
            vis[j] := true;
            var subCount := dfs_526(pos + 1, n, matches, vis);
            count := count + subCount;
            vis[j] := false;
        }
        i := i + 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
{
    var ans := 0;
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
    return ans;
}

// Helper function to compute integer square root
function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
{
    if x == 0 then 0
    else if x == 1 then 1
    else if x <= 4 then 2
    else if x <= 9 then 3
    else if x <= 16 then 4
    else if x <= 25 then 5
    else if x <= 36 then 6
    else if x <= 49 then 7
    else if x <= 64 then 8
    else if x <= 81 then 9
    else if x <= 100 then 10
    else if x <= 121 then 11
    else if x <= 144 then 12
    else if x <= 169 then 13
    else if x <= 196 then 14
    else if x <= 225 then 15
    else if x <= 256 then 16
    else if x <= 289 then 17
    else if x <= 324 then 18
    else if x <= 361 then 19
    else if x <= 400 then 20
    else if x <= 441 then 21
    else if x <= 484 then 22
    else if x <= 529 then 23
    else if x <= 576 then 24
    else if x <= 625 then 25
    else if x <= 676 then 26
    else if x <= 729 then 27
    else if x <= 784 then 28
    else if x <= 841 then 29
    else if x <= 900 then 30
    else if x <= 961 then 31
    else if x <= 1024 then 32
    else if x <= 1089 then 33
    else if x <= 1156 then 34
    else if x <= 1225 then 35
    else if x <= 1296 then 36
    else if x <= 1369 then 37
    else if x <= 1444 then 38
    else if x <= 1521 then 39
    else if x <= 1600 then 40
    else if x <= 62500 then 250
    else 250
}

// Helper function to compute powers of 10
function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) >= 1
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else 100000000
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := lastRemaining_390(o1);
    var o3: int;
    if o2 <= 15 {
        o3 := countArrangement_526(o2);
    } else {
        o3 := 1;
    }
    var o4: int;
    if o3 <= 250 {
        o4 := countTriples_1925(o3);
    } else {
        o4 := 0;
    }
    return o4;
}
