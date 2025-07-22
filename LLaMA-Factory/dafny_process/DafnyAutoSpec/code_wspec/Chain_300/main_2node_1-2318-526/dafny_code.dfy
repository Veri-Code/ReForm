
function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures gcd(a, b) <= a && gcd(a, b) <= b
    decreases if a >= b then a else b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function gcdHelper(a: int, b: int): int
    requires a > 0 && b >= 0
    ensures gcdHelper(a, b) > 0
    ensures gcdHelper(a, b) <= a
    ensures b > 0 ==> gcdHelper(a, b) <= b
    decreases b
{
    if b == 0 then a else gcdHelper(b, a % b)
}

function gcdSafe(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcdSafe(a, b) > 0
    ensures gcdSafe(a, b) <= a && gcdSafe(a, b) <= b
{
    if a >= b then gcdHelper(a, b) else gcdHelper(b, a)
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
    
    // Initialize base case for length 2
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            if gcdSafe(i + 1, j + 1) == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table for lengths 3 to n
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
                if gcdSafe(i + 1, j + 1) == 1 && i != j {
                    dp[k, i, j] := 0;
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                        invariant dp[k, i, j] >= 0
                        invariant dp[k, i, j] < mod
                    {
                        if gcdSafe(h + 1, i + 1) == 1 && h != i && h != j {
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
    
    // Sum all possibilities for the final answer
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant ans >= 0
        invariant ans < mod
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant ans >= 0
            invariant ans < mod
        {
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    
    return ans;
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
    
    // Build match array - for each position, which numbers can go there
    var matchArray := new seq<int>[n + 1];
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < |matchArray[k]| ==> 1 <= matchArray[k][j] <= n
    {
        var matches: seq<int> := [];
        var j := 1;
        while j <= n
            invariant 1 <= j <= n + 1
            invariant |matches| <= j - 1
            invariant forall idx :: 0 <= idx < |matches| ==> 1 <= matches[idx] <= n
        {
            if j % i == 0 || i % j == 0 {
                matches := matches + [j];
            }
            j := j + 1;
        }
        matchArray[i] := matches;
        i := i + 1;
    }
    
    var ans := dfs(1, n, vis, matchArray);
    return ans;
}

method dfs(pos: int, n: int, vis: array<bool>, matchArray: array<seq<int>>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    requires matchArray.Length == n + 1
    requires forall i :: 1 <= i <= n ==> forall j :: 0 <= j < |matchArray[i]| ==> 1 <= matchArray[i][j] <= n
    ensures count >= 0
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var i := 0;
    while i < |matchArray[pos]|
        invariant 0 <= i <= |matchArray[pos]|
        invariant count >= 0
    {
        var num := matchArray[pos][i];
        if !vis[num] {
            vis[num] := true;
            var subCount := dfs(pos + 1, n, vis, matchArray);
            count := count + subCount;
            vis[num] := false;
        }
        i := i + 1;
    }
}

method main_2node_1(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := distinctSequences_2318(o);
    // Since distinctSequences_2318 returns a value between 0 and 1000000006,
    // and countArrangement_526 requires input between 1 and 15,
    // we need to constrain o1 to be in the valid range
    var constrainedO1 := if o1 <= 15 && o1 >= 1 then o1 else (o1 % 15) + 1;
    var o2 := countArrangement_526(constrainedO1);
    return o2;
}
