
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 0 <= result <= 1000000000000000
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    
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
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        decreases temp
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
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
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant ans >= 0
                invariant cnt[i] >= 0
            {
                if ans <= 100000000000000 {
                    ans := ans * 10 + i;
                }
                count := count + 1;
            }
            i := i - 1;
        }
        result := ans;
    } else {
        // For positive numbers, arrange digits in ascending order
        // but avoid leading zeros
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
                invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
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
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant ans >= 0
                invariant cnt[i] >= 0
            {
                if ans <= 100000000000000 {
                    ans := ans * 10 + i;
                }
                count := count + 1;
            }
            i := i + 1;
        }
        result := ans;
    }
    
    // Ensure result is within bounds
    if result > 1000000000000000 {
        result := 1000000000000000;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
{
    if n == 0 {
        result := 0;
        return;
    }
    
    // Convert to array of digits
    var digits := new int[11]; // max 11 digits for safety
    var temp := n;
    var len := 0;
    
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
        result := 0;
        return;
    }
    
    // Reverse to get most significant digit first
    var i := 0;
    while i < len / 2
        invariant 0 <= i <= len / 2
        invariant len > 0
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
        invariant len > 0
    {
        i := i + 1;
    }
    
    if i < len {
        // Make it monotone increasing
        while i > 0 && i < len && digits[i - 1] > digits[i]
            invariant 0 <= i <= len
            invariant len > 0
        {
            if digits[i - 1] > 0 {
                digits[i - 1] := digits[i - 1] - 1;
            }
            i := i - 1;
        }
        i := i + 1;
        while i < len
            invariant 0 <= i <= len
            invariant len > 0
        {
            digits[i] := 9;
            i := i + 1;
        }
    }
    
    // Convert back to number
    result := 0;
    i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant result >= 0
        invariant len > 0
    {
        if result <= 100000000 && digits[i] >= 0 {
            result := result * 10 + digits[i];
        }
        i := i + 1;
    }
    
    // Ensure result is within bounds
    if result > n {
        result := n;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 2 <= result <= 100000
    decreases *
{
    var current := n;
    
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i * i <= temp && temp > 1
            invariant 2 <= i
            invariant temp >= 1
            invariant s >= 0
            decreases temp - i + 1
        {
            while temp % i == 0 && temp > 1
                invariant temp >= 1
                invariant s >= 0
                decreases temp
            {
                temp := temp / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            result := t;
            return;
        }
        current := s;
        if current < 2 { 
            result := 2;
            return;
        }
        if current > 100000 {
            result := 100000;
            return;
        }
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result <= 2147483647
{
    // Convert to digits
    var digits := new int[10]; // max 9 digits for 10^8
    var temp := num;
    var len := 0;
    
    while temp > 0 && len < 9
        invariant temp >= 0
        invariant 0 <= len <= 9
        decreases temp
    {
        digits[len] := temp % 10;
        temp := temp / 10;
        len := len + 1;
    }
    
    if len == 0 {
        result := 0;
        return;
    }
    
    // Reverse to get most significant digit first
    var i := 0;
    while i < len / 2
        invariant 0 <= i <= len / 2
        invariant len > 0
    {
        var tmp := digits[i];
        digits[i] := digits[len - 1 - i];
        digits[len - 1 - i] := tmp;
        i := i + 1;
    }
    
    // Calculate maximum (replace first non-9 with 9)
    var maxNum := 0;
    i := 0;
    var replaced := false;
    while i < len
        invariant 0 <= i <= len
        invariant maxNum >= 0
        invariant len > 0
    {
        if !replaced && digits[i] != 9 {
            if maxNum <= 214748364 {
                maxNum := maxNum * 10 + 9;
            } else {
                maxNum := 2147483647;
            }
            replaced := true;
        } else {
            if maxNum <= 214748364 && digits[i] >= 0 {
                maxNum := maxNum * 10 + digits[i];
            } else {
                maxNum := 2147483647;
            }
        }
        i := i + 1;
    }
    
    // Calculate minimum
    var minNum := 0;
    if len > 0 && digits[0] != 1 {
        // Replace first digit with 1
        minNum := 1;
        i := 1;
        while i < len
            invariant 1 <= i <= len
            invariant minNum >= 0
            invariant len > 0
        {
            if minNum <= 214748364 && digits[i] >= 0 {
                minNum := minNum * 10 + digits[i];
            }
            i := i + 1;
        }
    } else {
        // First digit is 1, find first digit that's not 0 or 1
        minNum := if len > 0 then 1 else 0;
        i := 1;
        var replaced2 := false;
        while i < len
            invariant 1 <= i <= len
            invariant minNum >= 0
            invariant len > 0
        {
            if !replaced2 && digits[i] != 0 && digits[i] != 1 {
                if minNum <= 214748364 {
                    minNum := minNum * 10 + 0;
                }
                replaced2 := true;
            } else {
                if minNum <= 214748364 && digits[i] >= 0 {
                    minNum := minNum * 10 + digits[i];
                }
            }
            i := i + 1;
        }
    }
    
    result := if maxNum >= minNum then maxNum - minNum else 0;
    if result > 2147483647 {
        result := 2147483647;
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483647
    ensures result == -1 || result > n
{
    // Convert to digits
    var digits := new int[11]; // max 10 digits
    var temp := n;
    var len := 0;
    
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
        result := -1;
        return;
    }
    
    // Reverse to get most significant digit first
    var i := 0;
    while i < len / 2
        invariant 0 <= i <= len / 2
        invariant len > 0
    {
        var tmp := digits[i];
        digits[i] := digits[len - 1 - i];
        digits[len - 1 - i] := tmp;
        i := i + 1;
    }
    
    // Find rightmost character that is smaller than next character
    i := len - 2;
    while i >= 0 && i < len - 1 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len
        invariant len > 0
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    // Find ceiling of digits[i] in right part
    var j := len - 1;
    while j > i && digits[i] >= digits[j]
        invariant i < j < len
        invariant len > 0
        decreases j
    {
        j := j - 1;
    }
    
    // Swap
    var tmp := digits[i];
    digits[i] := digits[j];
    digits[j] := tmp;
    
    // Reverse the right part
    var left := i + 1;
    var right := len - 1;
    while left < right
        invariant i + 1 <= left <= right + 1 <= len
        invariant len > 0
    {
        tmp := digits[left];
        digits[left] := digits[right];
        digits[right] := tmp;
        left := left + 1;
        right := right - 1;
    }
    
    // Convert back to number
    var ans := 0;
    i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant ans >= 0
        invariant len > 0
    {
        if ans <= 214748364 && digits[i] >= 0 {
            ans := ans * 10 + digits[i];
        } else {
            ans := 2147483647;
        }
        i := i + 1;
    }
    
    if ans > 2147483647 || ans <= n {
        result := -1;
    } else {
        result := ans;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result == -1 || result >= 1
    decreases *
{
    var o1 := smallestNumber_2165(o);
    
    // Clamp o1 to valid range for next function
    if o1 < 0 { o1 := 0; }
    if o1 > 1000000000 { o1 := 1000000000; }
    
    var o2 := monotoneIncreasingDigits_738(o1);
    
    // Ensure o2 is valid for smallestValue_2507
    if o2 < 2 { o2 := 2; }
    if o2 > 100000 { o2 := 100000; }
    
    var o3 := smallestValue_2507(o2);
    
    // Ensure o3 is valid for maxDiff_1432
    if o3 < 1 { o3 := 1; }
    if o3 > 100000000 { o3 := 100000000; }
    
    var o4 := maxDiff_1432(o3);
    
    // Ensure o4 is valid for nextGreaterElement_556
    if o4 < 1 { o4 := 1; }
    if o4 > 2147483647 { o4 := 2147483647; }
    
    result := nextGreaterElement_556(o4);
}
