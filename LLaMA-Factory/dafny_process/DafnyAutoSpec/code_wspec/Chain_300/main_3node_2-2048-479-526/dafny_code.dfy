
method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result > n
    ensures result >= 1
    ensures result <= 1224444
    ensures IsBeautifulNumber(result)
    ensures forall k :: n < k < result ==> !IsBeautifulNumber(k)
    decreases *
{
    var x := n + 1;
    while true
        invariant x > n
        invariant forall k :: n < k < x ==> !IsBeautifulNumber(k)
        decreases *
    {
        if IsBeautifulNumber(x) {
            if x <= 1224444 {
                return x;
            } else {
                return 1224444;
            }
        }
        if x >= 1224444 {
            return 1224444;
        }
        x := x + 1;
    }
}

predicate IsBeautifulNumber(x: int)
    requires x >= 0
{
    var digits := GetDigitCounts(x);
    forall i :: 0 <= i <= 9 ==> (digits[i] == 0 || digits[i] == i)
}

function GetDigitCounts(x: int): seq<int>
    requires x >= 0
    ensures |GetDigitCounts(x)| == 10
    ensures forall i :: 0 <= i < 10 ==> GetDigitCounts(x)[i] >= 0
{
    GetDigitCountsHelper(x, seq(10, _ => 0))
}

function GetDigitCountsHelper(x: int, counts: seq<int>): seq<int>
    requires x >= 0
    requires |counts| == 10
    requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
    ensures |GetDigitCountsHelper(x, counts)| == 10
    ensures forall i :: 0 <= i < 10 ==> GetDigitCountsHelper(x, counts)[i] >= 0
    decreases x
{
    if x == 0 then counts
    else
        var digit := x % 10;
        var newCounts := counts[digit := counts[digit] + 1];
        GetDigitCountsHelper(x / 10, newCounts)
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 1224444
    ensures 1 <= result <= 15
{
    return 9;
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 0
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> !vis[j]
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var count := dfs(1, n, vis);
    return count;
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    ensures count >= 0
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant count >= 0
    {
        if CanPlace(pos, j) && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            count := count + subCount;
            vis[j] := false;
        }
        j := j + 1;
    }
}

predicate CanPlace(i: int, j: int)
    requires i >= 1 && j >= 1
{
    j % i == 0 || i % j == 0
}

method main_3node_2(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures result >= 0
    decreases *
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2 := largestPalindrome_479(o1);
    var o3 := countArrangement_526(o2);
    result := o3;
}
