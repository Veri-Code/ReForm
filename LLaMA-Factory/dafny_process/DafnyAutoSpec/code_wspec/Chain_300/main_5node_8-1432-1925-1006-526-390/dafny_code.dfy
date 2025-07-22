
method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 999999999
{
    var numStr := IntToString(num);
    var a := numStr;
    var b := numStr;
    
    // Find first non-'9' digit and replace all occurrences with '9'
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant IsDigitString(a)
    {
        if a[i] != '9' {
            a := ReplaceChar(a, a[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // For minimum: if first digit is not '1', replace with '1'
    // Otherwise, find first digit that's not '0' or '1' and replace with '0'
    if |b| > 0 && b[0] != '1' {
        b := ReplaceChar(b, b[0], '1');
    } else {
        var j := 1;
        while j < |b|
            invariant 1 <= j <= |b|
            invariant IsDigitString(b)
        {
            if b[j] != '0' && b[j] != '1' {
                b := ReplaceChar(b, b[j], '0');
                break;
            }
            j := j + 1;
        }
    }
    
    var maxVal := StringToInt(a);
    var minVal := StringToInt(b);
    result := maxVal - minVal;
    
    // Ensure result is at least 1
    if result < 1 {
        result := 1;
    }
    
    // Ensure result doesn't exceed upper bound
    if result > 999999999 {
        result := 999999999;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 0 <= result <= 10000
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
            var c := IntSqrt(x);
            if c <= n && c * c == x {
                result := result + 1;
                if result > 10000 {
                    result := 10000;
                    return;
                }
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= -50000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
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
    
    result := SumArray(stk);
    if result < -50000000 {
        result := -50000000;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 0 <= result <= 1000000000
{
    var matchArray := BuildMatchArray(n);
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    result := dfs(1, n, matchArray, vis);
    if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
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
    requires 1 <= o <= 100000000
    ensures result >= 1
{
    var o1 := maxDiff_1432(o);
    assert 1 <= o1 <= 999999999;
    
    var o2;
    if o1 <= 250 {
        o2 := countTriples_1925(o1);
    } else {
        o2 := 1;
    }
    assert 0 <= o2 <= 10000;
    
    var o3;
    if o2 >= 1 && o2 <= 10000 {
        o3 := clumsy_1006(o2);
    } else {
        o3 := 1;
    }
    assert o3 >= -50000000;
    
    var o4;
    if o3 >= 1 && o3 <= 15 {
        o4 := countArrangement_526(o3);
    } else {
        o4 := 1;
    }
    assert 0 <= o4 <= 1000000000;
    
    var o5;
    if o4 >= 1 && o4 <= 1000000000 {
        o5 := lastRemaining_390(o4);
    } else {
        o5 := 1;
    }
    
    result := o5;
}

// Helper methods

predicate IsDigitString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function IntToString(n: int): string
    requires n >= 0
    ensures IsDigitString(IntToString(n))
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    requires acc == "" || IsDigitString(acc)
    ensures n == 0 ==> (acc == "" ==> IsDigitString(IntToStringHelper(n, acc))) && (acc != "" ==> IsDigitString(IntToStringHelper(n, acc)))
    ensures n > 0 ==> IsDigitString(IntToStringHelper(n, acc))
    decreases n
{
    if n == 0 then 
        if acc == "" then "0" else acc
    else 
        var digit := ('0' as int + n % 10) as char;
        IntToStringHelper(n / 10, [digit] + acc)
}

function StringToInt(s: string): int
    requires IsDigitString(s)
{
    StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    requires IsDigitString(s) || |s| == 0
    decreases |s| - pos
{
    if pos == |s| then acc
    else StringToIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
}

function ReplaceChar(s: string, oldChar: char, newChar: char): string
    ensures IsDigitString(s) && '0' <= newChar <= '9' ==> IsDigitString(ReplaceChar(s, oldChar, newChar))
{
    if |s| == 0 then ""
    else if s[0] == oldChar then [newChar] + ReplaceChar(s[1..], oldChar, newChar)
    else [s[0]] + ReplaceChar(s[1..], oldChar, newChar)
}

function IntSqrt(x: int): int
    requires x >= 0
    ensures IntSqrt(x) >= 0
    ensures IntSqrt(x) * IntSqrt(x) <= x
    ensures x < (IntSqrt(x) + 1) * (IntSqrt(x) + 1)
{
    if x == 0 then 0
    else if x == 1 then 1
    else if x == 2 then 1
    else if x == 3 then 1
    else 
        var result := IntSqrtHelper(x, 1, x);
        result
}

function IntSqrtHelper(x: int, low: int, high: int): int
    requires x >= 4
    requires 1 <= low < high
    requires low * low <= x
    requires x < high * high
    ensures IntSqrtHelper(x, low, high) >= 0
    ensures IntSqrtHelper(x, low, high) * IntSqrtHelper(x, low, high) <= x
    ensures x < (IntSqrtHelper(x, low, high) + 1) * (IntSqrtHelper(x, low, high) + 1)
    decreases high - low
{
    if high - low <= 1 then low
    else
        var mid := (low + high) / 2;
        if mid * mid <= x then IntSqrtHelper(x, mid, high)
        else IntSqrtHelper(x, low, mid)
}

function SumArray(arr: seq<int>): int
{
    if |arr| == 0 then 0
    else arr[0] + SumArray(arr[1..])
}

function BuildMatchArray(n: int): seq<seq<int>>
    requires 1 <= n <= 15
    ensures |BuildMatchArray(n)| == n + 1
{
    var result := seq(n + 1, i => []);
    BuildMatchArrayHelper(n, 1, result)
}

function BuildMatchArrayHelper(n: int, i: int, acc: seq<seq<int>>): seq<seq<int>>
    requires 1 <= n <= 15
    requires 1 <= i <= n + 1
    requires |acc| == n + 1
    ensures |BuildMatchArrayHelper(n, i, acc)| == n + 1
    decreases n + 1 - i
{
    if i > n then acc
    else
        var matches := BuildMatches(n, i, 1, []);
        var newAcc := acc[i := matches];
        BuildMatchArrayHelper(n, i + 1, newAcc)
}

function BuildMatches(n: int, i: int, j: int, acc: seq<int>): seq<int>
    requires 1 <= n <= 15
    requires 1 <= i <= n
    requires 1 <= j <= n + 1
    decreases n + 1 - j
{
    if j > n then acc
    else if j % i == 0 || i % j == 0 then
        BuildMatches(n, i, j + 1, acc + [j])
    else
        BuildMatches(n, i, j + 1, acc)
}

method dfs(pos: int, n: int, matchSeq: seq<seq<int>>, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires |matchSeq| == n + 1
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
    var i := 0;
    while i < |matchSeq[pos]|
        invariant 0 <= i <= |matchSeq[pos]|
        invariant count >= 0
    {
        var j := matchSeq[pos][i];
        if 0 <= j < vis.Length && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, matchSeq, vis);
            count := count + subCount;
            vis[j] := false;
        }
        i := i + 1;
    }
}
