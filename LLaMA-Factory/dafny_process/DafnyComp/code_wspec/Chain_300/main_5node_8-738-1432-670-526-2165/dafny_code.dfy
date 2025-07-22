
method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
    ensures result <= 1000000000
{
    if n == 0 {
        result := 0;
        return;
    }
    
    var s := intToDigits(n);
    var i := 1;
    
    while i < |s| && s[i-1] <= s[i]
        invariant 1 <= i <= |s|
        invariant forall k :: 0 <= k < i-1 ==> s[k] <= s[k+1]
    {
        i := i + 1;
    }
    
    if i < |s| {
        while i > 0 && i < |s| && s[i-1] > s[i]
            invariant 0 <= i < |s|
            invariant |s| > 0
            invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
        {
            if s[i-1] > '0' {
                var newDigit := (s[i-1] as int - 1) as char;
                if '0' <= newDigit <= '9' {
                    s := s[i-1 := newDigit];
                }
            }
            i := i - 1;
        }
        i := i + 1;
        while i < |s|
            invariant i <= |s|
            invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
        {
            s := s[i := '9'];
            i := i + 1;
        }
    }
    
    result := digitsToInt(s);
    if result > n {
        result := n;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result <= 100000000
{
    var digits := intToDigits(num);
    var maxDigits := digits;
    var minDigits := digits;
    
    // For maximum: replace first non-9 digit with 9
    var i := 0;
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
        invariant forall k :: 0 <= k < |maxDigits| ==> '0' <= maxDigits[k] <= '9'
    {
        if maxDigits[i] != '9' {
            var oldChar := maxDigits[i];
            maxDigits := replaceChar(maxDigits, oldChar, '9');
            break;
        }
        i := i + 1;
    }
    
    // For minimum: replace appropriately
    if minDigits[0] != '1' {
        var oldChar := minDigits[0];
        minDigits := replaceChar(minDigits, oldChar, '1');
    } else {
        i := 1;
        while i < |minDigits|
            invariant 1 <= i <= |minDigits|
            invariant forall k :: 0 <= k < |minDigits| ==> '0' <= minDigits[k] <= '9'
        {
            if minDigits[i] != '0' && minDigits[i] != '1' {
                var oldChar := minDigits[i];
                minDigits := replaceChar(minDigits, oldChar, '0');
                break;
            }
            i := i + 1;
        }
    }
    
    var maxVal := digitsToInt(maxDigits);
    var minVal := digitsToInt(minDigits);
    result := if maxVal >= minVal then maxVal - minVal else 0;
    if result > 100000000 {
        result := 100000000;
    }
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures 0 <= result <= 100000000
{
    var s := intToDigits(num);
    var n := |s|;
    if n == 0 {
        result := num;
        return;
    }
    
    var d := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> d[k] == k
    {
        d[i] := i;
        i := i + 1;
    }
    
    i := n - 2;
    while i >= 0
        invariant -1 <= i < n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        if s[i] <= s[d[i + 1]] {
            d[i] := d[i + 1];
        }
        i := i - 1;
    }
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    {
        var j := d[i];
        if s[i] < s[j] {
            var temp := s[i];
            s := s[i := s[j]];
            s := s[j := temp];
            break;
        }
        i := i + 1;
    }
    
    result := digitsToInt(s);
    if result > 100000000 {
        result := 100000000;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 0 <= result <= 1000000000000000
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    result := dfs(1, n, vis);
    if result > 1000000000000000 {
        result := 1000000000000000;
    }
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
        count := 1;
        return;
    }
    
    count := 0;
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant count >= 0
    {
        if (j % pos == 0 || pos % j == 0) && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            count := count + subCount;
            vis[j] := false;
        }
        j := j + 1;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures -1000000000000000 <= result <= 1000000000000000
{
    var neg := num < 0;
    var absNum := if num < 0 then -num else num;
    
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
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    if absNum == 0 {
        result := 0;
        return;
    }
    
    result := 0;
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant result >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
                invariant result >= 0
            {
                if result <= 100000000000000 {
                    result := result * 10 + i;
                }
                j := j + 1;
            }
            i := i - 1;
        }
        if result <= 1000000000000000 {
            result := -result;
        } else {
            result := -1000000000000000;
        }
    } else {
        if cnt[0] > 0 {
            i := 1;
            while i < 10
                invariant 1 <= i <= 10
            {
                if cnt[i] > 0 {
                    result := i;
                    cnt[i] := cnt[i] - 1;
                    break;
                }
                i := i + 1;
            }
        }
        
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant result >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
                invariant result >= 0
            {
                if result <= 100000000000000 {
                    result := result * 10 + i;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        if result > 1000000000000000 {
            result := 1000000000000000;
        }
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures -1000000000000000 <= result <= 1000000000000000
    decreases *
{
    var o1 := monotoneIncreasingDigits_738(o);
    var o1_clamped := if o1 < 1 then 1 else if o1 > 100000000 then 100000000 else o1;
    var o2 := maxDiff_1432(o1_clamped);
    var o2_clamped := if o2 < 0 then 0 else if o2 > 100000000 then 100000000 else o2;
    var o3 := maximumSwap_670(o2_clamped);
    var o3_clamped := if o3 < 1 then 1 else if o3 > 15 then 15 else o3;
    var o4 := countArrangement_526(o3_clamped);
    result := smallestNumber_2165(o4);
    
    // Ensure result is within bounds
    if result < -1000000000000000 {
        result := -1000000000000000;
    } else if result > 1000000000000000 {
        result := 1000000000000000;
    }
}

// Helper methods for digit manipulation
method intToDigits(n: int) returns (digits: seq<char>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
{
    if n == 0 {
        digits := ['0'];
        return;
    }
    
    digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp == 0 ==> |digits| >= 1
    {
        var digit := temp % 10;
        var digitChar := (digit + '0' as int) as char;
        digits := [digitChar] + digits;
        temp := temp / 10;
    }
}

method digitsToInt(digits: seq<char>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
    {
        result := result * 10 + (digits[i] as int - '0' as int);
        i := i + 1;
    }
}

method replaceChar(s: seq<char>, oldChar: char, newChar: char) returns (result: seq<char>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> 
        (s[i] == oldChar ==> result[i] == newChar) &&
        (s[i] != oldChar ==> result[i] == s[i])
    ensures forall i :: 0 <= i < |s| && '0' <= s[i] <= '9' && '0' <= newChar <= '9' ==> '0' <= result[i] <= '9'
{
    result := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            (s[j] == oldChar ==> result[j] == newChar) &&
            (s[j] != oldChar ==> result[j] == s[j])
        invariant forall j :: 0 <= j < i && '0' <= s[j] <= '9' && '0' <= newChar <= '9' ==> '0' <= result[j] <= '9'
    {
        if s[i] == oldChar {
            result := result + [newChar];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}
