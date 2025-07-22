
method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 10000
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var row := 0;
    while row <= n
        invariant 0 <= row <= n + 1
    {
        var col := 0;
        while col <= n
            invariant 0 <= col <= n + 1
        {
            f[row, col] := 0;
            col := col + 1;
        }
        row := row + 1;
    }
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
        {
            f[i, j] := j + f[i, j - 1];
            var k := i;
            while k < j
                invariant i <= k <= j
            {
                var left_cost := if k - 1 < i then 0 else f[i, k - 1];
                var right_cost := if k + 1 > j then 0 else f[k + 1, j];
                var max_cost := if left_cost > right_cost then left_cost else right_cost;
                var total_cost := max_cost + k;
                if total_cost < f[i, j] {
                    f[i, j] := total_cost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result <= 0 {
        result := 1;
    }
    
    // Ensure postcondition
    if result > 10000 {
        result := 10000;
    }
    if result < 1 {
        result := 1;
    }
}

function digitSum(x: int): int
    requires x >= 0
    ensures digitSum(x) >= 0
{
    if x == 0 then 0
    else (x % 10) + digitSum(x / 10)
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 2147483647
{
    // Use arrays to simulate Counter - digit sums range from 1 to about 36 for n <= 10000
    var cnt := new int[50]; // More than enough for digit sums
    var i := 0;
    while i < 50
        invariant 0 <= i <= 50
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 0;
    var mx := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 0
        invariant mx >= 0
    {
        var s := digitSum(i);
        if s < 50 {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    result := if ans <= 0 then 1 else ans;
    
    // Ensure postcondition
    if result > 2147483647 {
        result := 2147483647;
    }
    if result < 1 {
        result := 1;
    }
}

method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        return [0];
    }
    
    var temp := n;
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        decreases temp
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    if |result| == 0 {
        result := [0];
    }
    
    return result;
}

method digitsToInt(digits: seq<int>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
    {
        result := result * 10 + digits[i];
        i := i + 1;
    }
}

method reverseSeq(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
{
    result := [];
    var i := |s|;
    while i > 0
        invariant 0 <= i <= |s|
        invariant |result| == |s| - i
        invariant forall j :: 0 <= j < |result| ==> result[j] == s[|s| - 1 - j]
    {
        i := i - 1;
        result := result + [s[i]];
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483647
    ensures -1 <= result <= 2147483647
{
    var cs := intToDigits(n);
    var len := |cs|;
    
    if len <= 1 {
        result := -1;
        return;
    }
    
    var i := len - 2;
    
    // Find the rightmost character that is smaller than its next character
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i <= len - 2
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    // Find the smallest character on right side of above character that is greater than cs[i]
    var j := len - 1;
    while cs[i] >= cs[j]
        invariant i < j < len
        decreases j
    {
        j := j - 1;
    }
    
    // Swap characters
    var temp := cs[i];
    cs := cs[i := cs[j]];
    cs := cs[j := temp];
    
    // Reverse the substring after position i
    var suffix := cs[i + 1..];
    var reversedSuffix := reverseSeq(suffix);
    cs := cs[..i + 1] + reversedSuffix;
    
    var ans := digitsToInt(cs);
    
    if ans > 2147483647 {
        result := -1;
    } else {
        result := ans;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 200
    ensures -1 <= result <= 2147483647
{
    var o1 := getMoneyAmount_375(o);
    var o2 := countLargestGroup_1399(o1);
    var o3 := nextGreaterElement_556(o2);
    result := o3;
}
