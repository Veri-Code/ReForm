
method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 1000000007
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall k :: 0 <= k < i ==> f[k] == 0
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant f[0] == 1
        invariant forall k :: 1 <= k < j ==> 1 <= f[k] <= mod
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        if f[j] == 0 { f[j] := mod; }
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant f[0] == 1
        invariant f[1] >= 1
        invariant forall k :: 0 <= k < j ==> 1 <= f[k] <= mod
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        if f[j] == 0 { f[j] := mod; }
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k < j ==> 1 <= f[k] <= mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            if f[j] == 0 { f[j] := mod; }
            j := j + 1;
        }
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
        if ans == 0 { ans := mod; }
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
        if ans == 0 { ans := mod; }
    }
    
    result := ans;
}

method isPrime(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    if x == 2 {
        return true;
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

method reverse(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    var res := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
    result := res;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 1000000007
    ensures result >= 0
    ensures result <= 100000000
{
    var current := n;
    if current > 100000000 {
        result := 100000000;
        return;
    }
    
    while current <= 100000000
        invariant current >= n
        invariant current <= 100000000 + 1
        decreases 100000000 - current + 1
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                result := current;
                return;
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    
    result := 100000000;
}

method intToString(num: int) returns (s: seq<char>)
    requires num >= 0
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if num == 0 {
        return ['0'];
    }
    
    var digits := [];
    var temp := num;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| >= 1
        decreases temp
    {
        var digit := temp % 10;
        var digitChar := ('0' as int + digit) as char;
        digits := [digitChar] + digits;
        temp := temp / 10;
    }
    s := digits;
}

method stringToInt(s: seq<char>) returns (result: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    result := res;
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= 0
{
    var s := intToString(num);
    var n := |s|;
    var d := new int[n];
    
    // Initialize d array
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> d[k] == k
    {
        d[i] := i;
        i := i + 1;
    }
    
    // Fill d array from right to left
    if n >= 2 {
        i := n - 2;
        while i >= 0
            invariant -1 <= i <= n - 2
            invariant forall k :: i + 1 <= k < n ==> 0 <= d[k] < n
            invariant d[n-1] == n-1
            invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
        {
            if s[i] <= s[d[i + 1]] {
                d[i] := d[i + 1];
            }
            i := i - 1;
        }
    }
    
    // Find first position to swap
    i := 0;
    var swapped := false;
    while i < n && !swapped
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
        invariant |s| == n >= 1
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        var j := d[i];
        if i < |s| && j < |s| && s[i] < s[j] {
            // Perform swap
            var temp := s[i];
            s := s[i := s[j]];
            s := s[j := temp];
            swapped := true;
        }
        i := i + 1;
    }
    
    var finalResult := stringToInt(s);
    result := finalResult;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000
    ensures result >= 0
{
    var o1 := numberOfWays_3183(o);
    var o2 := primePalindrome_866(o1);
    var o3 := maximumSwap_670(o2);
    result := o3;
}
