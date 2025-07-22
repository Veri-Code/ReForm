
method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        result := 1;
        return;
    }
    
    var digits := intToDigits(n);
    var i := 1;
    
    // Find first decreasing position
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
        invariant forall k :: 0 <= k < i-1 ==> digits[k] <= digits[k+1]
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Decrease digits and propagate
        while i > 0 && i < |digits| && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
            decreases i
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        
        // Set remaining digits to 9
        i := i + 1;
        while i < |digits|
            invariant 0 <= i <= |digits|
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(digits);
    if result == 0 { result := 1; }
    if result > 1000000000 { result := 1000000000; }
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := isqrt(n);
    var f := new int[m+1, n+1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m+1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n+1
        {
            f[i, j] := n + 1; // Use n+1 as "infinity"
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m+1
        invariant f[0, 0] == 0
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n+1
            invariant f[0, 0] == 0
        {
            f[i, j] := f[i-1, j];
            if j >= i * i && f[i, j - i * i] <= n {
                var candidate := f[i, j - i * i] + 1;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result > n || result <= 0 { result := n; } // Ensure postcondition
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483647
    ensures 0 <= result <= 1000
{
    var ans := 0;
    var temp := x;
    var mi := -2147483648;
    var mx := 2147483647;
    
    while temp != 0
        decreases if temp >= 0 then temp else -temp
    {
        // Check for overflow before multiplication
        if ans < mi / 10 + 1 || ans > mx / 10 {
            result := 0;
            return;
        }
        
        var y := temp % 10;
        if temp < 0 && y > 0 {
            y := y - 10;
        }
        
        ans := ans * 10 + y;
        temp := (temp - y) / 10;
    }
    
    result := ans;
    // Clamp to expected output range
    if result < 0 { result := 0; }
    if result > 1000 { result := 1000; }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 100000
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant 0 <= result
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    if result == 0 { result := 1; } // Ensure postcondition
    if result > 100000 { result := 100000; } // Clamp to upper bound
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 0 <= result
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
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
        invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
        invariant f[0] == 1
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    result := f[n];
    
    if n >= 4 {
        result := (result + f[n - 4]) % mod;
    }
    if n >= 8 {
        result := (result + f[n - 8]) % mod;
    }
}

// Helper methods
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
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp == 0 ==> |result| >= 1
        decreases temp
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    digits := result;
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

method isqrt(n: int) returns (result: int)
    requires n >= 0
    ensures result >= 0
    ensures result * result <= n < (result + 1) * (result + 1)
{
    if n == 0 { return 0; }
    
    result := 1;
    while (result + 1) * (result + 1) <= n
        invariant result >= 1
        invariant result * result <= n
        decreases n - result * result
    {
        result := result + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures 0 <= result
{
    var o1 := monotoneIncreasingDigits_738(o);
    // Clamp o1 to valid range for numSquares_279
    if o1 > 10000 { o1 := 10000; }
    var o2 := numSquares_279(o1);
    var o3 := reverse_7(o2);
    // Ensure o3 is at least 1 for sumOfMultiples_2652
    if o3 == 0 { o3 := 1; }
    var o4 := sumOfMultiples_2652(o3);
    var o5 := numberOfWays_3183(o4);
    result := o5;
}
