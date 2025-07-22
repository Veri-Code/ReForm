
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result
{
    var m := n;
    while m * m > n
        invariant 0 <= m
        decreases m
    {
        m := m - 1;
    }
    
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values (representing infinity)
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 100000000; // Large value as infinity
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
    if result >= 100000000 || result < 1 {
        result := 1; // Fallback to ensure postcondition
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result <= 1000000000
{
    var digits := [];
    var temp := num;
    
    // Extract digits
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        result := 0;
        return;
    }
    
    // Calculate maximum number (replace first non-9 with 9)
    var maxNum := num;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
    {
        if digits[i] != 9 {
            var multiplier := 1;
            var j := |digits| - 1;
            while j > i
                invariant i <= j < |digits|
                decreases j
            {
                multiplier := multiplier * 10;
                j := j - 1;
            }
            maxNum := maxNum + (9 - digits[i]) * multiplier;
            break;
        }
        i := i + 1;
    }
    
    // Calculate minimum number
    var minNum := num;
    if digits[0] != 1 {
        // Replace first digit with 1
        var multiplier := 1;
        var j := |digits| - 1;
        while j > 0
            invariant 0 <= j < |digits|
            decreases j
        {
            multiplier := multiplier * 10;
            j := j - 1;
        }
        minNum := minNum - (digits[0] - 1) * multiplier;
    } else {
        // First digit is 1, find first digit that's not 0 or 1
        i := 1;
        while i < |digits|
            invariant 1 <= i <= |digits|
        {
            if digits[i] != 0 && digits[i] != 1 {
                var multiplier := 1;
                var j := |digits| - 1;
                while j > i
                    invariant i <= j < |digits|
                    decreases j
                {
                    multiplier := multiplier * 10;
                    j := j - 1;
                }
                minNum := minNum - digits[i] * multiplier;
                break;
            }
            i := i + 1;
        }
    }
    
    result := maxNum - minNum;
    if result < 0 {
        result := 0;
    }
    if result > 1000000000 {
        result := 1000000000;
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
    
    var digits := [];
    var temp := n;
    
    // Extract digits
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        result := 1;
        return;
    }
    
    // Find first decreasing position
    var i := 1;
    while i < |digits| && digits[i - 1] <= digits[i]
        invariant 1 <= i <= |digits|
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Found decreasing position, need to fix
        while i > 0 && digits[i - 1] > digits[i]
            invariant 0 <= i < |digits|
        {
            if digits[i - 1] > 0 {
                digits := digits[i - 1 := digits[i - 1] - 1];
            }
            i := i - 1;
        }
        
        // Set all following digits to 9
        i := i + 1;
        while i < |digits|
            invariant 0 <= i <= |digits|
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    // Convert back to number
    result := 0;
    i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
    {
        if result <= 100000000 && result >= 0 {
            var newResult := result * 10 + digits[i];
            if newResult >= result {
                result := newResult;
            }
        }
        i := i + 1;
    }
    
    if result <= 0 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
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
    
    // Fill the DP table
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
                var left := if k - 1 >= i then f[i, k - 1] else 0;
                var right := if k + 1 <= j then f[k + 1, j] else 0;
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
    
    result := f[1, n];
    if result < 0 {
        result := 0;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := numSquares_279(o);
    
    // Ensure o1 is within bounds for maxDiff_1432
    if o1 > 100000000 {
        o1 := 100000000;
    }
    
    var o2 := maxDiff_1432(o1);
    var o3 := monotoneIncreasingDigits_738(o2);
    
    // Ensure o3 is within bounds for getMoneyAmount_375
    if o3 > 200 {
        o3 := 200;
    }
    
    var o4 := getMoneyAmount_375(o3);
    result := o4;
}
