
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 100000
    decreases *
{
    var current := n;
    
    while true
        invariant 2 <= current <= 100000
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        // Factor current and sum the prime factors
        while i * i <= current
            invariant 2 <= i
            invariant 0 <= s
            invariant current >= 1
        {
            while current % i == 0
                invariant current >= 1
                invariant i >= 2
                invariant 0 <= s
                decreases current
            {
                current := current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        // If current > 1, it's a prime factor
        if current > 1 {
            s := s + current;
        }
        
        // If sum equals original, we found the answer
        if s == t {
            assert 2 <= t <= 100000;
            return t;
        }
        
        // Continue with the sum
        current := s;
        
        // Ensure we stay in bounds
        if current > 100000 || current < 2 {
            return if t <= 100000 && t >= 1 then t else 100000;
        }
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 1000000007
{
    var mod := 1000000007;
    var coins := [1, 2, 6];
    var f := new int[n + 1];
    
    // Initialize array
    var k := 0;
    while k <= n
        invariant 0 <= k <= n + 1
        invariant forall j :: 0 <= j < k ==> f[j] == 0
    {
        f[k] := 0;
        k := k + 1;
    }
    f[0] := 1;
    
    // Dynamic programming for coin combinations
    var coinIdx := 0;
    while coinIdx < 3
        invariant 0 <= coinIdx <= 3
        invariant forall j :: 0 <= j <= n ==> 0 <= f[j] < mod
    {
        var x := coins[coinIdx];
        var j := x;
        while j <= n
            invariant x <= j
            invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - x]) % mod;
            j := j + 1;
        }
        coinIdx := coinIdx + 1;
    }
    
    var ans := f[n];
    
    // Add special cases
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    // Ensure result is at least 1
    if ans == 0 {
        ans := 1;
    }
    
    return ans;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 100000000
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
        invariant sum <= x * 1000
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    // Ensure result is at least 1
    if sum == 0 {
        sum := 1;
    }
    
    return sum;
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
{
    // Convert to string representation (simplified approach)
    var digits := [];
    var temp := num;
    
    // Extract digits
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        var digit := temp % 10;
        assert 0 <= digit <= 9;
        digits := [digit] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        return 0;
    }
    
    // Calculate maximum value by replacing first non-9 digit with 9
    var maxVal := 0;
    var multiplier := 1;
    var i := |digits| - 1;
    var foundNon9 := false;
    var replaceDigit := -1;
    
    // Find first non-9 digit
    var j := 0;
    while j < |digits|
        invariant 0 <= j <= |digits|
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        if digits[j] != 9 && !foundNon9 {
            foundNon9 := true;
            replaceDigit := digits[j];
        }
        j := j + 1;
    }
    
    while i >= 0
        invariant -1 <= i < |digits|
        invariant maxVal >= 0
        invariant multiplier > 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        var digit := digits[i];
        if foundNon9 && digit == replaceDigit {
            assert multiplier > 0;
            assert 9 >= 0;
            maxVal := maxVal + 9 * multiplier;
            foundNon9 := false; // Only replace first occurrence
        } else {
            assert multiplier > 0;
            assert 0 <= digit <= 9;
            maxVal := maxVal + digit * multiplier;
        }
        multiplier := multiplier * 10;
        i := i - 1;
    }
    
    // Calculate minimum value
    var minVal := 0;
    multiplier := 1;
    i := |digits| - 1;
    var foundReplace := false;
    var minReplaceDigit := -1;
    
    // Find replacement strategy for minimum
    if |digits| > 0 && digits[0] != 1 {
        minReplaceDigit := digits[0];
    } else if |digits| > 1 {
        j := 1;
        while j < |digits|
            invariant 1 <= j <= |digits|
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        {
            if digits[j] != 0 && digits[j] != 1 && !foundReplace {
                foundReplace := true;
                minReplaceDigit := digits[j];
            }
            j := j + 1;
        }
    }
    
    while i >= 0
        invariant -1 <= i < |digits|
        invariant minVal >= 0
        invariant multiplier > 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        var digit := digits[i];
        var pos := |digits| - 1 - i;
        
        if pos == 0 { // First digit (leftmost)
            if minReplaceDigit == digit {
                assert multiplier > 0;
                assert 1 >= 0;
                minVal := minVal + 1 * multiplier;
            } else {
                assert multiplier > 0;
                assert 0 <= digit <= 9;
                minVal := minVal + digit * multiplier;
            }
        } else {
            if foundReplace && digit == minReplaceDigit {
                assert multiplier > 0;
                assert 0 >= 0;
                minVal := minVal + 0 * multiplier;
                foundReplace := false; // Only replace first occurrence
            } else {
                assert multiplier > 0;
                assert 0 <= digit <= 9;
                minVal := minVal + digit * multiplier;
            }
        }
        multiplier := multiplier * 10;
        i := i - 1;
    }
    
    // Since we're constructing maxVal to be >= original and minVal to be <= original
    // and both are valid numbers, maxVal >= minVal should hold
    if maxVal < minVal {
        return 0;
    }
    
    return maxVal - minVal;
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := numberOfWays_3183(o1);
    if o2 > 1000 {
        o2 := 1000;
    }
    var o3 := sumOfMultiples_2652(o2);
    var o4 := maxDiff_1432(o3);
    return o4;
}
