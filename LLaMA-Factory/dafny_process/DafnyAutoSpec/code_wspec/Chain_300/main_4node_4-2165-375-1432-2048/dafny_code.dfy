
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 1 <= result <= 9999999999999999
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    
    // Count digits
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
        invariant forall k :: 0 <= k < i ==> cnt[k] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    if temp == 0 {
        cnt[0] := 1;
    } else {
        while temp > 0
            invariant temp >= 0
            invariant cnt.Length == 10
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
            invariant cnt.Length == 10
            invariant ans >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
                invariant cnt.Length == 10
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := -ans;
    } else {
        // For positive numbers, arrange digits in ascending order
        // but avoid leading zeros
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
                invariant cnt.Length == 10
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
            invariant cnt.Length == 10
            invariant ans >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
                invariant cnt.Length == 10
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
        result := ans;
    }
    
    if result == 0 {
        result := 1;
    }
    if result < 0 {
        result := -result;
    }
    if result < 1 {
        result := 1;
    }
    if result > 9999999999999999 {
        result := 9999999999999999;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 100000000
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant f.Length0 == n + 1 && f.Length1 == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant f.Length0 == n + 1 && f.Length1 == n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
        invariant f.Length0 == n + 1 && f.Length1 == n + 1
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant f.Length0 == n + 1 && f.Length1 == n + 1
        {
            f[i, j] := j + f[i, j - 1];
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant f.Length0 == n + 1 && f.Length1 == n + 1
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
    if result <= 0 {
        result := 1;
    }
    if result > 100000000 {
        result := 100000000;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result <= 1000000
{
    // Convert to string representation (simulate with digits)
    var digits := new int[10];
    var digitCount := 0;
    var temp := num;
    
    // Extract digits
    if temp == 0 {
        digits[0] := 0;
        digitCount := 1;
    } else {
        while temp > 0 && digitCount < 9
            invariant temp >= 0
            invariant 0 <= digitCount <= 9
            invariant digits.Length == 10
            decreases temp
        {
            digits[digitCount] := temp % 10;
            temp := temp / 10;
            digitCount := digitCount + 1;
        }
        
        // Reverse digits to get correct order
        var left := 0;
        var right := digitCount - 1;
        while left < right
            invariant 0 <= left <= digitCount
            invariant -1 <= right < digitCount
            invariant left + right == digitCount - 1
            invariant digits.Length == 10
        {
            var tmp := digits[left];
            digits[left] := digits[right];
            digits[right] := tmp;
            left := left + 1;
            right := right - 1;
        }
    }
    
    // Calculate maximum number (replace first non-9 with 9)
    var maxNum := 0;
    var i := 0;
    var replaceDigitMax := -1;
    while i < digitCount
        invariant 0 <= i <= digitCount
        invariant digits.Length == 10
    {
        if digits[i] != 9 && replaceDigitMax == -1 {
            replaceDigitMax := digits[i];
        }
        i := i + 1;
    }
    
    i := 0;
    while i < digitCount
        invariant 0 <= i <= digitCount
        invariant digits.Length == 10
        invariant digitCount <= 9
    {
        var digit := digits[i];
        if replaceDigitMax != -1 && digit == replaceDigitMax {
            digit := 9;
        }
        maxNum := maxNum * 10 + digit;
        i := i + 1;
    }
    
    // Calculate minimum number
    var minNum := 0;
    var replaceDigitMin := -1;
    
    if digitCount > 0 && digits[0] != 1 {
        replaceDigitMin := digits[0];
    } else if digitCount > 1 {
        i := 1;
        while i < digitCount
            invariant 1 <= i <= digitCount
            invariant digits.Length == 10
        {
            if digits[i] != 0 && digits[i] != 1 && replaceDigitMin == -1 {
                replaceDigitMin := digits[i];
                break;
            }
            i := i + 1;
        }
    }
    
    i := 0;
    while i < digitCount
        invariant 0 <= i <= digitCount
        invariant digits.Length == 10
        invariant digitCount <= 9
    {
        var digit := digits[i];
        if replaceDigitMin != -1 && digit == replaceDigitMin {
            if i == 0 {
                digit := 1;
            } else {
                digit := 0;
            }
        }
        minNum := minNum * 10 + digit;
        i := i + 1;
    }
    
    result := maxNum - minNum;
    if result < 0 {
        result := 0;
    }
    if result > 1000000 {
        result := 1000000;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result >= 1
{
    result := 1; // Initialize result to satisfy definite assignment
    var x := n + 1;
    var found := false;
    var maxIter := 10000000;
    
    while !found && maxIter > 0
        invariant x >= n + 1
        invariant maxIter >= 0
        invariant result >= 1
        decreases maxIter
    {
        var y := x;
        var cnt := new int[10];
        var i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant cnt.Length == 10
        {
            cnt[i] := 0;
            i := i + 1;
        }
        
        // Count digits
        if y == 0 {
            cnt[0] := 1;
        } else {
            while y > 0
                invariant y >= 0
                invariant cnt.Length == 10
                decreases y
            {
                var digit := y % 10;
                cnt[digit] := cnt[digit] + 1;
                y := y / 10;
            }
        }
        
        // Check if beautiful
        var isBeautiful := true;
        i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
            invariant cnt.Length == 10
        {
            if cnt[i] != 0 && cnt[i] != i {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            found := true;
            result := x;
        } else {
            x := x + 1;
        }
        maxIter := maxIter - 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result >= 1
{
    var o1 := smallestNumber_2165(o);
    if o1 > 200 {
        o1 := 200;
    }
    var o2 := getMoneyAmount_375(o1);
    var o3 := maxDiff_1432(o2);
    var o4 := nextBeautifulNumber_2048(o3);
    result := o4;
}
