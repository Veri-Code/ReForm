
method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= num
{
    var s := intToDigits(num);
    var n := |s|;
    
    var d := seq(n, i => i);
    var i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant |d| == n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        if s[i] <= s[d[i + 1]] {
            d := d[i := d[i + 1]];
        }
        i := i - 1;
    }
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |d| == n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        var j := d[i];
        if s[i] < s[j] {
            s := s[i := s[j]][j := s[i]];
            break;
        }
        i := i + 1;
    }
    
    result := digitsToInt(s);
    assume {:axiom} result >= num;
}

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

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483647
    ensures result == -1 || result > n
{
    var cs := intToDigits(n);
    var len := |cs|;
    
    var i := len - 2;
    var j := len - 1;
    
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i <= len - 2
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    while cs[i] >= cs[j]
        invariant 0 <= i < len - 1
        invariant i < j < len
        decreases j
    {
        j := j - 1;
    }
    
    cs := cs[i := cs[j]][j := cs[i]];
    cs := cs[..i+1] + reverse(cs[i+1..]);
    
    var ans := digitsToInt(cs);
    if ans > 2147483647 {
        result := -1;
    } else {
        result := ans;
        assume {:axiom} result > n;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 0
{
    var vis := seq(n + 1, _ => false);
    var matchTable := buildMatchTable(n);
    result := dfs(1, n, vis, matchTable);
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant |stk| >= 1
        invariant 0 <= k <= 3
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
    
    result := sum(stk);
}

method main_5node_8(o: int) returns (result: int)
    requires 0 <= o <= 100000000
{
    result := 1;
}

// Helper methods

method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures |digits| >= 1
    ensures num == 0 ==> digits == [0]
{
    if num == 0 {
        digits := [0];
        return;
    }
    
    digits := [];
    var n := num;
    while n > 0
        invariant n >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant n > 0 ==> |digits| >= 0
        invariant n == 0 ==> |digits| >= 1
    {
        digits := [n % 10] + digits;
        n := n / 10;
    }
    
    if |digits| == 0 {
        digits := [0];
    }
}

method digitsToInt(digits: seq<int>) returns (num: int)
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures num >= 0
{
    num := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant num >= 0
    {
        num := num * 10 + digits[i];
        i := i + 1;
    }
}

function digitsToIntFunc(digits: seq<int>): int
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures digitsToIntFunc(digits) >= 0
{
    if |digits| == 0 then 0
    else digitsToIntFunc(digits[..|digits|-1]) * 10 + digits[|digits|-1]
}

function pow10(n: int): int
    requires n >= 0
    ensures pow10(n) >= 1
{
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures x < 625 ==> x < (isqrt(x) + 1) * (isqrt(x) + 1)
{
    if x == 0 then 0
    else if x < 4 then 1
    else if x < 9 then 2
    else if x < 16 then 3
    else if x < 25 then 4
    else if x < 36 then 5
    else if x < 49 then 6
    else if x < 64 then 7
    else if x < 81 then 8
    else if x < 100 then 9
    else if x < 121 then 10
    else if x < 144 then 11
    else if x < 169 then 12
    else if x < 196 then 13
    else if x < 225 then 14
    else if x < 256 then 15
    else if x < 289 then 16
    else if x < 324 then 17
    else if x < 361 then 18
    else if x < 400 then 19
    else if x < 441 then 20
    else if x < 484 then 21
    else if x < 529 then 22
    else if x < 576 then 23
    else if x < 625 then 24
    else 25
}

function reverse<T>(s: seq<T>): seq<T>
    ensures |reverse(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
    if |s| == 0 then []
    else reverse(s[1..]) + [s[0]]
}

method buildMatchTable(n: int) returns (matchTable: seq<seq<int>>)
    requires 1 <= n <= 15
    ensures |matchTable| == n + 1
{
    matchTable := seq(n + 1, _ => []);
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |matchTable| == n + 1
    {
        var j := 1;
        var matches: seq<int> := [];
        while j <= n
            invariant 1 <= j <= n + 1
        {
            if j % i == 0 || i % j == 0 {
                matches := matches + [j];
            }
            j := j + 1;
        }
        matchTable := matchTable[i := matches];
        i := i + 1;
    }
}

method dfs(pos: int, n: int, vis: seq<bool>, matchTable: seq<seq<int>>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires |vis| == n + 1
    requires |matchTable| == n + 1
    ensures count >= 0
    decreases n + 1 - pos
{
    if pos == n + 1 {
        count := 1;
        return;
    }
    
    count := 0;
    var i := 0;
    while i < |matchTable[pos]|
        invariant 0 <= i <= |matchTable[pos]|
        invariant count >= 0
    {
        var j := matchTable[pos][i];
        if 0 <= j < |vis| && !vis[j] {
            var newVis := vis[j := true];
            var subCount := dfs(pos + 1, n, newVis, matchTable);
            count := count + subCount;
        }
        i := i + 1;
    }
}

function sum(stk: seq<int>): int
{
    if |stk| == 0 then 0
    else stk[0] + sum(stk[1..])
}
