
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures if num >= 0 then result >= 0 else result < 0
{
    var neg := num < 0;
    var absNum := if num >= 0 then num else -num;
    
    // Count digits
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall k :: 0 <= k < i ==> cnt[k] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := absNum;
    if temp == 0 {
        cnt[0] := 1;
    } else {
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
            decreases temp
        {
            var digit := temp % 10;
            cnt[digit] := cnt[digit] + 1;
            temp := temp / 10;
        }
    }
    
    var ans := 0;
    if neg {
        // For negative numbers, arrange digits in descending order
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant ans >= 0
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
                invariant ans >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := -ans;
        // Ensure result is negative when num is negative
        if result == 0 {
            result := -1;
        }
    } else {
        // For positive numbers, arrange digits in ascending order
        // But handle leading zeros
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
            {
                i := i + 1;
            }
            if i < 10 {
                ans := i;
                cnt[i] := cnt[i] - 1;
            }
        }
        
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant ans >= 0
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
                invariant ans >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
        result := ans;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 1
{
    // Build compatibility matrix
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
    
    result := dfs_526(1, n, matchArray, vis);
    
    // Ensure result is at least 1
    if result == 0 {
        result := 1;
    }
}

method dfs_526(pos: int, n: int, matchArray: array<seq<int>>, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires matchArray.Length == n + 1
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
    while i < |matchArray[pos]|
        invariant 0 <= i <= |matchArray[pos]|
        invariant count >= 0
    {
        var j := matchArray[pos][i];
        if 1 <= j <= n && !vis[j] {
            vis[j] := true;
            var subCount := dfs_526(pos + 1, n, matchArray, vis);
            count := count + subCount;
            vis[j] := false;
        }
        i := i + 1;
    }
}

method isPrime(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method reverseNumber(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    result := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant result >= 0
        decreases temp
    {
        result := result * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= 2
    decreases *
{
    var current := n;
    
    // Handle base cases where we know the answer
    if current <= 2 {
        return 2;
    }
    
    while true
        invariant current >= n
        decreases *
    {
        var rev := reverseNumber(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                return current;
            }
        }
        
        // Skip even-length palindromes between 10^7 and 10^8 (optimization from original)
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

method main_3node_2(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result >= 2
    decreases *
{
    var o1 := smallestNumber_2165(o);
    
    // Ensure o1 is in valid range for countArrangement_526
    var o1_clamped := if o1 < 1 then 1 else if o1 > 15 then 15 else o1;
    var o2 := countArrangement_526(o1_clamped);
    
    // Ensure o2 is in valid range for primePalindrome_866
    var o2_clamped := if o2 < 1 then 1 else if o2 > 100000000 then 100000000 else o2;
    result := primePalindrome_866(o2_clamped);
}
