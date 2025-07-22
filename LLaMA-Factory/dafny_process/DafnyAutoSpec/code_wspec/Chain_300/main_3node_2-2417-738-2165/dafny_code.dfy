
method countDigits(n: int) returns (evenCount: int, oddCount: int, totalDigits: int)
    requires n >= 0
    ensures evenCount >= 0 && oddCount >= 0 && totalDigits >= 0
    ensures evenCount + oddCount == totalDigits
    ensures n == 0 ==> totalDigits == 1
    ensures n > 0 ==> totalDigits > 0
{
    evenCount := 0;
    oddCount := 0;
    totalDigits := 0;
    var t := n;
    
    if t == 0 {
        evenCount := 1; // 0 is even
        totalDigits := 1;
        return;
    }
    
    while t > 0
        invariant evenCount >= 0 && oddCount >= 0 && totalDigits >= 0
        invariant evenCount + oddCount == totalDigits
        invariant t >= 0
        invariant n > 0 && t == 0 ==> totalDigits > 0
    {
        var digit := t % 10;
        if digit % 2 == 1 {
            oddCount := oddCount + 1;
        } else {
            evenCount := evenCount + 1;
        }
        t := t / 10;
        totalDigits := totalDigits + 1;
    }
}

method power10(k: int) returns (result: int)
    requires k >= 0
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
    ensures result >= 0
    decreases 1000000000 - n
{
    var evenCount, oddCount, totalDigits := countDigits(n);
    
    if totalDigits % 2 == 1 {
        // Odd number of digits - construct next even-digit fair number
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
    } else if evenCount == oddCount {
        result := n;
    } else {
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := n; // fallback to avoid infinite recursion
        }
    }
}

method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures n == 0 ==> digits == [0]
    ensures n > 0 ==> |digits| > 0
{
    if n == 0 {
        digits := [0];
        return;
    }
    
    digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp == 0 ==> |digits| >= 1
    {
        var digit := temp % 10;
        digits := [digit] + digits;
        temp := temp / 10;
    }
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

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n
    ensures result >= 0
{
    var digits := intToDigits(n);
    var s := digits; // mutable copy
    var i := 1;
    
    // Find first decreasing position
    while i < |s| && s[i-1] <= s[i]
        invariant 1 <= i <= |s|
    {
        i := i + 1;
    }
    
    if i < |s| {
        // Fix decreasing digits
        while i > 0 && s[i-1] > s[i]
            invariant 0 <= i < |s|
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            if s[i-1] > 0 {
                s := s[i-1 := s[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        
        // Set remaining digits to 9
        while i < |s|
            invariant 0 <= i <= |s|
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            s := s[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(s);
}

method smallestNumber_2165(num: int) returns (result: int)
{
    var neg := num < 0;
    var absNum := if num < 0 then -num else num;
    
    // Count digits
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    if absNum == 0 {
        cnt[0] := 1;
    } else {
        var temp := absNum;
        while temp > 0
            invariant temp >= 0
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var digit := temp % 10;
            cnt[digit] := cnt[digit] + 1;
            temp := temp / 10;
        }
    }
    
    result := 0;
    
    if neg {
        // For negative numbers, arrange digits in descending order
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
            {
                result := result * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := -result;
    } else {
        // For positive numbers, arrange digits in ascending order
        // but avoid leading zeros
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
            {
                i := i + 1;
            }
            if i < 10 {
                result := i;
                cnt[i] := cnt[i] - 1;
            }
        }
        
        // Add remaining digits in ascending order
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
            {
                result := result * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures true
{
    var o1 := closestFair_2417(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    result := smallestNumber_2165(o2);
}
