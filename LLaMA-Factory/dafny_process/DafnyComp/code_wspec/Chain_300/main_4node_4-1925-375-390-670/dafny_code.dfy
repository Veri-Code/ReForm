
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures 1 <= ans <= 200
{
    ans := 1; // Initialize to 1 to satisfy postcondition
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant 1 <= ans <= 200
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 1 <= ans <= 200
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                if ans < 200 {
                    ans := ans + 1;
                }
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x < (isqrt(x) + 1) * (isqrt(x) + 1)
{
    if x == 0 then 0
    else if x == 1 then 1
    else
        var mid := x / 2;
        var guess := isqrt_helper(x, 1, mid);
        guess
}

function isqrt_helper(x: int, low: int, high: int): int
    requires x >= 0
    requires low >= 0
    requires high >= low
    requires low * low <= x
    requires x < (high + 1) * (high + 1)
    ensures isqrt_helper(x, low, high) >= 0
    ensures isqrt_helper(x, low, high) * isqrt_helper(x, low, high) <= x < (isqrt_helper(x, low, high) + 1) * (isqrt_helper(x, low, high) + 1)
    decreases high - low
{
    if low >= high then low
    else
        var mid := (low + high + 1) / 2;
        if mid * mid <= x then
            isqrt_helper(x, mid, high)
        else
            isqrt_helper(x, low, mid - 1)
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 1000000000
{
    if n == 1 {
        result := 1;
        return;
    }
    
    var f := new int[n + 1, n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
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
                var left := if k - 1 < i then 0 else f[i, k - 1];
                var right := if k + 1 > j then 0 else f[k + 1, j];
                var cost := (if left > right then left else right) + k;
                if cost < f[i, j] {
                    f[i, j] := cost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := if f[1, n] <= 0 then 1 else f[1, n];
    if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 0 <= result <= 100000000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant a1 >= 1
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
    }
    
    result := if a1 <= 100000000 then a1 - 1 else 100000000;
    if result < 0 {
        result := 0;
    }
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= 0
{
    // Convert number to array of digits
    var digits := new int[10]; // Max 10 digits for numbers up to 100000000
    var temp := num;
    var len := 0;
    
    if num == 0 {
        digits[0] := 0;
        len := 1;
    } else {
        while temp > 0 && len < 10
            invariant temp >= 0
            invariant len >= 0
            invariant len <= 10
        {
            digits[len] := temp % 10;
            temp := temp / 10;
            len := len + 1;
        }
        
        // Reverse the digits array
        if len > 1 {
            var left := 0;
            var right := len - 1;
            while left < right
                invariant 0 <= left <= len
                invariant 0 <= right < len
                invariant left + right == len - 1
            {
                var tmp := digits[left];
                digits[left] := digits[right];
                digits[right] := tmp;
                left := left + 1;
                right := right - 1;
            }
        }
    }
    
    // Find the rightmost occurrence of the maximum digit for each position
    var d := new int[len];
    var i := 0;
    while i < len
        invariant 0 <= i <= len
    {
        d[i] := i;
        i := i + 1;
    }
    
    if len > 1 {
        i := len - 2;
        while i >= 0
            invariant -1 <= i < len
        {
            if i + 1 < len && 0 <= i < len && 0 <= d[i + 1] < len && digits[i] <= digits[d[i + 1]] {
                d[i] := d[i + 1];
            }
            i := i - 1;
        }
        
        // Find the first position where we can make a beneficial swap
        i := 0;
        while i < len
            invariant 0 <= i <= len
        {
            if i < len && 0 <= d[i] < len && digits[i] < digits[d[i]] {
                // Perform the swap
                var tmp := digits[i];
                digits[i] := digits[d[i]];
                digits[d[i]] := tmp;
                break;
            }
            i := i + 1;
        }
    }
    
    // Convert back to integer
    result := 0;
    i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant result >= 0
    {
        if result <= 214748364 && i < len {
            var new_result := result * 10 + digits[i];
            if new_result >= 0 {
                result := new_result;
            }
        }
        i := i + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures 0 <= result
{
    var o1 := countTriples_1925(o);
    var o2 := getMoneyAmount_375(o1);
    var o3 := lastRemaining_390(o2);
    var o4 := maximumSwap_670(o3);
    result := o4;
}
