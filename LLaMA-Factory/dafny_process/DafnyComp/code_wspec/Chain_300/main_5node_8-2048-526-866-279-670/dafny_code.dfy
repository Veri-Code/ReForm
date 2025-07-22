
method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 2000000
    ensures result > n
{
    var x := n + 1;
    while x <= 2000000
        invariant n + 1 <= x <= 2000001
        decreases 2000001 - x
    {
        var y := x;
        var cnt := new int[10];
        var i := 0;
        while i < 10
            invariant 0 <= i <= 10
        {
            cnt[i] := 0;
            i := i + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            y := y / 10;
            if digit < 10 {
                cnt[digit] := cnt[digit] + 1;
            }
        }
        
        var isBeautiful := true;
        i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && cnt[i] != i {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            return x;
        }
        x := x + 1;
    }
    return n + 1; // This ensures result > n
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 100000000
{
    var matchArray := new seq<int>[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        matchArray[i] := [];
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
                matchArray[i] := matchArray[i] + [j];
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
    
    var count := dfs_526(1, n, matchArray, vis);
    result := if count == 0 then 1 else count;
}

method dfs_526(pos: int, n: int, matchArray: array<seq<int>>, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires matchArray.Length == n + 1
    requires vis.Length == n + 1
    ensures count >= 0
    ensures count <= 100000000
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
        invariant count <= 100000000
    {
        var j := matchArray[pos][i];
        if 1 <= j <= n && !vis[j] {
            vis[j] := true;
            var subCount := dfs_526(pos + 1, n, matchArray, vis);
            if count <= 100000000 - subCount {
                count := count + subCount;
            } else {
                count := 100000000;
            }
            vis[j] := false;
        }
        i := i + 1;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 200000000
    ensures result >= n
{
    var current := n;
    while current <= 200000000
        invariant n <= current <= 200000001
        decreases 200000001 - current
    {
        if isPalindrome(current) && isPrime(current) {
            return current;
        }
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    return n; // This ensures result >= n
}

function isPalindrome(x: int): bool
    requires x >= 0
{
    x == reverseNumber(x)
}

function reverseNumber(x: int): int
    requires x >= 0
    decreases x
{
    if x < 10 then x
    else (x % 10) * power10(countDigits(x) - 1) + reverseNumber(x / 10)
}

function countDigits(x: int): int
    requires x >= 0
    ensures countDigits(x) >= 1
    decreases x
{
    if x < 10 then 1 else 1 + countDigits(x / 10)
}

function power10(n: int): int
    requires n >= 0
    ensures power10(n) >= 1
    decreases n
{
    if n == 0 then 1 else 10 * power10(n - 1)
}

function isPrime(x: int): bool
    requires x >= 0
{
    x >= 2 && forall k :: 2 <= k < x ==> x % k != 0
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var dp := new int[n + 1];
    dp[0] := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant dp[0] == 0
        invariant forall k :: 1 <= k < i ==> 1 <= dp[k] <= k
    {
        dp[i] := i; // worst case: all 1s
        i := i + 1;
    }
    
    var square := 1;
    while square * square <= n
        invariant 1 <= square
        invariant dp[0] == 0
        invariant forall k :: 1 <= k <= n ==> 1 <= dp[k] <= k
        decreases n + 1 - square * square
    {
        var j := square * square;
        while j <= n
            invariant square * square <= j <= n + 1
            invariant dp[0] == 0
            invariant forall k :: 1 <= k <= n ==> 1 <= dp[k] <= k
            decreases n + 1 - j
        {
            if dp[j - square * square] + 1 < dp[j] {
                dp[j] := dp[j - square * square] + 1;
            }
            j := j + 1;
        }
        square := square + 1;
    }
    
    result := dp[n];
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= 0
{
    if num == 0 {
        return 0;
    }
    
    var digits := numberToDigits(num);
    var n := |digits|;
    
    if n <= 1 {
        return num;
    }
    
    var maxIndices := new int[n];
    maxIndices[n - 1] := n - 1;
    
    var i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant forall k :: i + 1 <= k < n ==> 0 <= maxIndices[k] < n
    {
        if digits[i] <= digits[maxIndices[i + 1]] {
            maxIndices[i] := maxIndices[i + 1];
        } else {
            maxIndices[i] := i;
        }
        i := i - 1;
    }
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        if digits[i] < digits[maxIndices[i]] {
            // Swap
            var temp := digits[i];
            digits := digits[i := digits[maxIndices[i]]];
            digits := digits[maxIndices[i] := temp];
            break;
        }
        i := i + 1;
    }
    
    result := digitsToNumber(digits);
}

function numberToDigits(num: int): seq<int>
    requires num >= 0
    ensures |numberToDigits(num)| >= 1
    ensures forall i :: 0 <= i < |numberToDigits(num)| ==> 0 <= numberToDigits(num)[i] <= 9
{
    if num < 10 then [num]
    else numberToDigits(num / 10) + [num % 10]
}

function digitsToNumber(digits: seq<int>): int
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures digitsToNumber(digits) >= 0
{
    if |digits| == 1 then digits[0]
    else digits[0] * power10(|digits| - 1) + digitsToNumber(digits[1..])
}

method main_5node_8(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures 0 <= result
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2: int;
    if o1 <= 15 {
        o2 := countArrangement_526(o1);
    } else {
        o2 := 1;
    }
    var o3 := primePalindrome_866(o2);
    var o4: int;
    if o3 <= 10000 {
        o4 := numSquares_279(o3);
    } else {
        o4 := 1;
    }
    var o5 := maximumSwap_670(o4);
    result := o5;
}
