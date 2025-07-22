
method isPrime(x: int) returns (result: bool)
    requires x >= 0
    ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
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
    
    // Need to prove that no divisors exist from v to x-1
    assert forall k :: 2 <= k < v ==> x % k != 0;
    assert v * v > x;
    
    // For any k >= v, if k < x and x % k == 0, then x / k < v
    // But x / k is also a divisor, and we've checked all divisors < v
    assert forall k :: v <= k < x ==> x % k != 0 by {
        forall k | v <= k < x
            ensures x % k != 0
        {
            if x % k == 0 {
                var quotient := x / k;
                assert quotient * k == x;
                assert quotient >= 1;
                if quotient == 1 {
                    assert k == x;
                    assert false;
                } else {
                    assert quotient >= 2;
                    assert quotient * k == x;
                    assert k >= v;
                    assert quotient * v <= quotient * k == x;
                    assert quotient <= x / v;
                    assert v * v > x;
                    assert quotient < v;
                    assert x % quotient == 0;
                    assert false;
                }
            }
        }
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
    return res;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 100000000
    ensures result >= n
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        invariant current >= 1
        invariant current <= 100000000
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                return current;
            }
        }
        
        // Special case optimization from Python code
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            if current < 100000000 {
                current := current + 1;
            } else {
                return current; // Must be 100000000 which is in valid range
            }
        }
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 2147483648
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> f[j] == 0
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
        invariant forall k :: 1 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    var ans := f[n];
    
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    return if ans == 0 then 1 else ans;
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures -1 <= result <= 10000
{
    // Convert number to sequence of digits
    var digits := new int[11]; // Max 11 digits for safety
    var temp := n;
    var len := 0;
    
    // Extract digits
    while temp > 0 && len < 10
        invariant temp >= 0
        invariant len >= 0
        invariant len <= 10
        decreases temp
    {
        digits[len] := temp % 10;
        temp := temp / 10;
        len := len + 1;
    }
    
    if len == 0 {
        return -1;
    }
    
    // Reverse to get correct order
    var i := 0;
    while i < len / 2
        invariant 0 <= i <= len / 2
    {
        var temp_digit := digits[i];
        digits[i] := digits[len - 1 - i];
        digits[len - 1 - i] := temp_digit;
        i := i + 1;
    }
    
    // Find pivot
    i := len - 2;
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len - 1
        decreases i + 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    // Find successor
    var j := len - 1;
    while digits[i] >= digits[j]
        invariant i < j < len
        decreases j - i
    {
        j := j - 1;
    }
    
    // Swap
    var temp_digit := digits[i];
    digits[i] := digits[j];
    digits[j] := temp_digit;
    
    // Reverse suffix
    var left := i + 1;
    var right := len - 1;
    while left < right
        invariant i + 1 <= left <= right + 1 <= len
        decreases right - left
    {
        temp_digit := digits[left];
        digits[left] := digits[right];
        digits[right] := temp_digit;
        left := left + 1;
        right := right - 1;
    }
    
    // Convert back to number with overflow check
    var ans := 0;
    i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant ans >= 0
    {
        if ans > 214748364 {
            return -1;
        }
        if ans == 214748364 && digits[i] > 7 {
            return -1;
        }
        var new_ans := ans * 10 + digits[i];
        if new_ans < 0 {
            return -1;
        }
        ans := new_ans;
        i := i + 1;
    }
    
    return if ans > 10000 then -1 else ans;
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    if n <= 0 {
        return 1;
    }
    
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant m >= 0
        invariant m * m <= n
        decreases n - m * m
    {
        m := m + 1;
    }
    
    var f := new int[n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> f[j] == n + 1
    {
        f[i] := n + 1; // Large value instead of infinity
        i := i + 1;
    }
    f[0] := 0;
    
    // DP computation
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f[0] == 0
        invariant forall j :: 0 <= j <= n ==> 0 <= f[j] <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant f[0] == 0
            invariant forall k :: 0 <= k <= n ==> 0 <= f[k] <= n + 1
        {
            if j >= i * i {
                var newVal := f[j - i * i] + 1;
                if newVal < f[j] {
                    f[j] := newVal;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    return if f[n] >= 1 then f[n] else 1;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 1
    decreases *
{
    var o1 := primePalindrome_866(o);
    
    // Ensure o1 is within bounds for numberOfWays_3183
    var o2;
    if o1 <= 100000 {
        o2 := numberOfWays_3183(o1);
    } else {
        o2 := numberOfWays_3183(100000);
    }
    
    var o3 := nextGreaterElement_556(o2);
    
    // Ensure o3 is within bounds for numSquares_279
    var o4;
    if o3 >= 1 && o3 <= 10000 {
        o4 := numSquares_279(o3);
    } else {
        o4 := numSquares_279(1);
    }
    
    return o4;
}
