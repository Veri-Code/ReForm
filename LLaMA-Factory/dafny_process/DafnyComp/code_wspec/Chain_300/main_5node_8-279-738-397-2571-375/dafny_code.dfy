
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= n
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant 0 <= m
        invariant m * m <= n
        decreases n - m * m
    {
        m := m + 1;
    }
    
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
        invariant forall x, y :: 0 <= x < i && 0 <= y <= n ==> f[x, y] == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall y :: 0 <= y < j ==> f[i, y] == n + 1
            invariant forall x, y :: 0 <= x < i && 0 <= y <= n ==> f[x, y] == n + 1
        {
            f[i, j] := n + 1;
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f[0, 0] == 0
        invariant forall x, y :: 0 <= x < i && 0 <= y <= n ==> 0 <= f[x, y] <= n + 1
        invariant forall y :: 1 <= y <= n ==> f[0, y] == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall y :: 0 <= y < j ==> 0 <= f[i, y] <= n + 1
            invariant forall x, y :: 0 <= x < i && 0 <= y <= n ==> 0 <= f[x, y] <= n + 1
            invariant f[0, 0] == 0
            invariant forall y :: 1 <= y <= n ==> f[0, y] == n + 1
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
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        result := 1;
        return;
    }
    
    var digits := new int[10];
    var len := 0;
    var temp := n;
    
    // Extract digits
    while temp > 0 && len < 10
        invariant temp >= 0
        invariant 0 <= len <= 10
        decreases temp
    {
        digits[len] := temp % 10;
        temp := temp / 10;
        len := len + 1;
    }
    
    if len == 0 {
        result := 1;
        return;
    }
    
    // Reverse to get most significant digit first
    var i := 0;
    while i < len / 2
        invariant 0 <= i <= len / 2
    {
        var tmp := digits[i];
        digits[i] := digits[len - 1 - i];
        digits[len - 1 - i] := tmp;
        i := i + 1;
    }
    
    // Find first decreasing position
    i := 1;
    while i < len && digits[i - 1] <= digits[i]
        invariant 1 <= i <= len
    {
        i := i + 1;
    }
    
    if i < len {
        // Make monotone increasing
        while i > 0 && digits[i - 1] > digits[i]
            invariant 0 <= i <= len
        {
            digits[i - 1] := digits[i - 1] - 1;
            i := i - 1;
        }
        i := i + 1;
        while i < len
            invariant 0 <= i <= len
        {
            digits[i] := 9;
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
        if result <= 100000000 {
            var new_result := result * 10 + digits[i];
            if new_result >= 0 && new_result <= 1000000000 {
                result := new_result;
            }
        }
        i := i + 1;
    }
    
    // Ensure result is at least 1
    if result < 1 {
        result := 1;
    }
    
    // Ensure result is within bounds
    if result > 1000000000 {
        result := 1000000000;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 99999
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 99999
        decreases 99999 - ans
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    if current == 1 {
        result := ans + 1;
    } else {
        result := 100000;
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 200
{
    var ans := 0;
    var cnt := 0;
    var current := n;
    
    while current > 0
        invariant current >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases current
    {
        if current % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        current := current / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans + 1;
    
    // Ensure result is within bounds
    if result < 1 {
        result := 1;
    }
    if result > 200 {
        result := 200;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures result >= 0
{
    if n == 1 {
        result := 0;
        return;
    }
    
    var f := new int[n + 1, n + 1];
    
    // Initialize
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
        decreases i
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
                var left_cost := if k - 1 >= i then f[i, k - 1] else 0;
                var right_cost := if k + 1 <= j then f[k + 1, j] else 0;
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
    if result < 0 {
        result := 0;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := numSquares_279(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    var o3 := integerReplacement_397(o2);
    var o4 := minOperations_2571(o3);
    var o5 := getMoneyAmount_375(o4);
    result := o5;
}
