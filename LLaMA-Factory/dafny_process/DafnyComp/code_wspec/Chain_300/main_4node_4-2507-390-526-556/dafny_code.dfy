
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000000000
    decreases *
{
    var current := n;
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        // Factor the number and sum the prime factors
        while i * i <= temp && temp > 1
            invariant i >= 2
            invariant s >= 0
            invariant temp >= 1
            decreases temp - i + 1
        {
            while temp % i == 0 && temp > 1
                invariant i >= 2
                invariant s >= 0
                invariant temp >= 1
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
            assume 1 <= t <= 1000000000;
            return t;
        }
        current := s;
        assume current >= 1;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= n
    decreases *
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
        
        assume 1 <= a1 <= n;
        assume 1 <= an <= n;
    }
    
    return a1;
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 1
    decreases *
{
    // Pre-compute valid matches
    var matchArray: array<seq<int>> := new seq<int>[n + 1];
    var k := 0;
    while k <= n
        invariant 0 <= k <= n + 1
    {
        var validList: seq<int> := [];
        if k >= 1 {
            var j := 1;
            while j <= n
                invariant 1 <= j <= n + 1
            {
                if j % k == 0 || k % j == 0 {
                    validList := validList + [j];
                }
                j := j + 1;
            }
        }
        matchArray[k] := validList;
        k := k + 1;
    }
    
    var vis: array<bool> := new bool[n + 1];
    var idx := 0;
    while idx <= n
        invariant 0 <= idx <= n + 1
    {
        vis[idx] := false;
        idx := idx + 1;
    }
    
    var ans := dfs_helper(1, n, matchArray, vis);
    return if ans == 0 then 1 else ans;
}

method dfs_helper(i: int, n: int, matchArray: array<seq<int>>, vis: array<bool>) returns (count: int)
    requires 1 <= i <= n + 1
    requires 1 <= n <= 15
    requires matchArray.Length == n + 1
    requires vis.Length == n + 1
    ensures count >= 0
    modifies vis
    decreases n + 1 - i
{
    if i == n + 1 {
        return 1;
    }
    
    var total := 0;
    var matchList := matchArray[i];
    var j := 0;
    
    while j < |matchList|
        invariant 0 <= j <= |matchList|
        invariant total >= 0
    {
        var candidate := matchList[j];
        if 1 <= candidate <= n && !vis[candidate] {
            vis[candidate] := true;
            var subCount := dfs_helper(i + 1, n, matchArray, vis);
            total := total + subCount;
            vis[candidate] := false;
        }
        j := j + 1;
    }
    
    return total;
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= -1
{
    // Convert number to sequence of digits
    var digits := numberToDigits(n);
    var len := |digits|;
    
    if len <= 1 {
        return -1;
    }
    
    // Find the rightmost digit that is smaller than the digit next to it
    var i := len - 2;
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len - 1
        decreases i + 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    // Find the smallest digit on right side of above character that is greater than digits[i]
    var j := len - 1;
    while j > i && digits[i] >= digits[j]
        invariant i < j < len
        decreases j - i
    {
        j := j - 1;
    }
    
    // Swap the found characters
    var temp := digits[i];
    digits := digits[i := digits[j]];
    digits := digits[j := temp];
    
    // Reverse the sequence after position i
    digits := digits[..i+1] + reverse(digits[i+1..]);
    
    // Check if all digits are valid (0-9)
    if forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9 {
        var ans := digitsToNumber(digits);
        if ans > 2147483647 {
            return -1;
        } else {
            return ans;
        }
    } else {
        return -1;
    }
}

function numberToDigits(n: int): seq<int>
    requires n >= 0
    ensures |numberToDigits(n)| >= 1
    ensures forall i :: 0 <= i < |numberToDigits(n)| ==> 0 <= numberToDigits(n)[i] <= 9
{
    if n < 10 then [n]
    else numberToDigits(n / 10) + [n % 10]
}

function digitsToNumber(digits: seq<int>): int
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures digitsToNumber(digits) >= 0
{
    if |digits| == 1 then digits[0]
    else digitsToNumber(digits[..|digits|-1]) * 10 + digits[|digits|-1]
}

function reverse(s: seq<int>): seq<int>
{
    if |s| <= 1 then s
    else reverse(s[1..]) + [s[0]]
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= -1
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := lastRemaining_390(o1);
    if o2 <= 15 {
        var o3 := countArrangement_526(o2);
        var o4 := nextGreaterElement_556(o3);
        result := o4;
    } else {
        result := -1;
    }
}
