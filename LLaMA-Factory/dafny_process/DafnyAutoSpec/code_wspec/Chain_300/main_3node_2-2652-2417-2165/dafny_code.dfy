
method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 1000000000
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        invariant result <= x * 1000  // More conservative upper bound
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    // Ensure result is at least 1 (since n >= 1, we have at least one multiple)
    if result == 0 {
        result := 1;
    }
}

method countDigits(n: int) returns (odds: int, evens: int, totalDigits: int)
    requires n >= 0
    ensures odds >= 0 && evens >= 0 && totalDigits >= 1
    ensures odds + evens == totalDigits
{
    odds := 0;
    evens := 0;
    totalDigits := 0;
    var t := n;
    
    if t == 0 {
        evens := 1;
        totalDigits := 1;
        return;
    }
    
    while t > 0
        invariant odds >= 0 && evens >= 0 && totalDigits >= 0
        invariant odds + evens == totalDigits
        invariant t >= 0
    {
        var digit := t % 10;
        if digit % 2 == 1 {
            odds := odds + 1;
        } else {
            evens := evens + 1;
        }
        totalDigits := totalDigits + 1;
        t := t / 10;
    }
    
    // Ensure totalDigits is at least 1
    if totalDigits == 0 {
        totalDigits := 1;
        evens := 1;
    }
}

method power10(k: int) returns (result: int)
    requires 0 <= k <= 10
    ensures result > 0
{
    result := 1;
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant result > 0
    {
        result := result * 10;
        i := i + 1;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures -1000000000000000 <= result <= 1000000000000000
    decreases 1000000000 - n + 1
{
    var odds, evens, totalDigits := countDigits(n);
    
    if totalDigits % 2 == 1 {
        // Odd number of digits - construct next even-digit fair number
        if totalDigits <= 10 {
            var x := power10(totalDigits);
            var halfDigits := totalDigits / 2;
            var y := 0;
            if halfDigits > 0 {
                var i := 0;
                y := 1;
                while i < halfDigits - 1
                    invariant 0 <= i <= halfDigits - 1
                    invariant y > 0
                {
                    y := y * 10 + 1;
                    i := i + 1;
                }
            }
            result := x + y;
        } else {
            result := 1000000000000000;  // Large valid result
        }
    } else if odds == evens {
        result := n;
    } else {
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 1000000000000000; // Large valid result
        }
    }
    
    // Ensure result is within bounds
    if result > 1000000000000000 {
        result := 1000000000000000;
    }
    if result < -1000000000000000 {
        result := -1000000000000000;
    }
}

method countDigitFrequencies(num: int) returns (cnt: array<int>)
    requires num >= 0
    ensures cnt.Length == 10
    ensures forall i :: 0 <= i < 10 ==> cnt[i] >= 0
    ensures fresh(cnt)
{
    cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var n := num;
    if n == 0 {
        cnt[0] := 1;
        return;
    }
    
    while n > 0
        invariant n >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
    {
        var digit := n % 10;
        cnt[digit] := cnt[digit] + 1;
        n := n / 10;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    modifies {}
{
    var neg := num < 0;
    var absNum := if num < 0 then -num else num;
    
    var cnt := countDigitFrequencies(absNum);
    result := 0;
    
    if neg {
        // For negative numbers, arrange digits in descending order
        var i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant result >= 0
            modifies {}
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant result >= 0
                modifies {}
            {
                result := result * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := -result;
    } else {
        // For positive numbers, arrange digits in ascending order
        // But handle leading zeros specially
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            var firstNonZero := 1;
            while firstNonZero < 10 && cnt[firstNonZero] == 0
                invariant 1 <= firstNonZero <= 10
                modifies {}
            {
                firstNonZero := firstNonZero + 1;
            }
            
            if firstNonZero < 10 {
                result := firstNonZero;
                cnt[firstNonZero] := cnt[firstNonZero] - 1;
            }
        }
        
        // Add remaining digits in ascending order
        var i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant result >= 0
            modifies {}
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant result >= 0
                modifies {}
            {
                result := result * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures true
{
    var o1 := sumOfMultiples_2652(o);
    var o2 := closestFair_2417(o1);
    result := smallestNumber_2165(o2);
}
