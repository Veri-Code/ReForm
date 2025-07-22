
method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    ensures result <= 10000
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    // Count digits and classify as odd/even
    while t > 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        invariant t >= 0
        decreases t
    {
        if (t % 10) % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        // Odd number of digits
        result := 1000;
    } else if a == b {
        // Even number of digits and already fair
        result := n;
        if result > 10000 {
            result := 10000;
        }
    } else {
        // Even number of digits but not fair, recurse
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 1000;
        }
    }
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 100000000
{
    var m := isqrt(n);
    var f := new int[m + 1, n + 1];
    
    // Initialize with "infinity" (using a large value)
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := n + 1; // Large enough value as "infinity"
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
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
    if result > n {
        result := n;
    }
    // Ensure result is within bounds
    if result > 100000000 {
        result := 100000000;
    }
    // Ensure result is non-negative
    if result < 0 {
        result := 0;
    }
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= 0
    ensures result <= 100000
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    if n == 0 {
        result := 0;
        return;
    }
    
    var d := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> d[j] == j
    {
        d[i] := i;
        i := i + 1;
    }
    
    // Build the rightmost maximum index array
    i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    {
        if i + 1 < n && digits[i] <= digits[d[i + 1]] {
            d[i] := d[i + 1];
        }
        i := i - 1;
    }
    
    // Find first position to swap
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    {
        if i < n && d[i] < n && digits[i] < digits[d[i]] {
            // Perform swap
            digits := digits[i := digits[d[i]]][d[i] := digits[i]];
            break;
        }
        i := i + 1;
    }
    
    result := digitsToInt(digits);
    // Ensure result is within bounds
    if result > 100000 {
        result := 100000;
    }
    // Ensure result is non-negative
    if result < 0 {
        result := 0;
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires n >= 1
    ensures result >= 0
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases num
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            cnt := if cnt == 1 then 0 else 1;
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
    decreases *
{
    var o1 := closestFair_2417(o);
    var o2: int;
    if o1 <= 10000 {
        o2 := numSquares_279(o1);
    } else {
        o2 := 0;
    }
    
    var o3: int;
    if o2 <= 100000000 {
        o3 := maximumSwap_670(o2);
    } else {
        o3 := 0;
    }
    
    var o4: int;
    if o3 >= 1 {
        o4 := minOperations_2571(o3);
    } else {
        o4 := 0;
    }
    
    result := o4;
}

// Helper functions
function power10(n: int): int
    requires n >= 0
    ensures power10(n) >= 1
{
    if n == 0 then 1 else 10 * power10(n - 1)
}

method isqrt(n: int) returns (result: int)
    requires n >= 0
    ensures result >= 0
    ensures result * result <= n
{
    if n == 0 {
        result := 0;
        return;
    }
    
    var x := n;
    while x * x > n
        invariant x > 0
        decreases x
    {
        x := (x + n / x) / 2;
    }
    result := x;
}

method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if num == 0 {
        digits := [0];
        return;
    }
    
    var temp := num;
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        decreases temp
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    digits := result;
    // Ensure we have at least one digit
    if |digits| == 0 {
        digits := [0];
    }
}

method digitsToInt(digits: seq<int>) returns (result: int)
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
