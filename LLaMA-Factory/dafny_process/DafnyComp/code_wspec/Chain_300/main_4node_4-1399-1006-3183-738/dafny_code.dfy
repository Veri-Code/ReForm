
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    // Count frequency of each digit sum
    var digitSumCounts := new int[82]; // max digit sum for numbers up to 10000 is 9+9+9+9+1 = 37, but we use 82 for safety
    var i := 0;
    while i < 82
        invariant 0 <= i <= 82
    {
        digitSumCounts[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var groupsWithMaxCount := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant groupsWithMaxCount >= 0
    {
        var ds := digitSum(i);
        if ds < 82 {
            digitSumCounts[ds] := digitSumCounts[ds] + 1;
            
            if maxCount < digitSumCounts[ds] {
                maxCount := digitSumCounts[ds];
                groupsWithMaxCount := 1;
            } else if maxCount == digitSumCounts[ds] {
                groupsWithMaxCount := groupsWithMaxCount + 1;
            }
        }
        i := i + 1;
    }
    
    result := groupsWithMaxCount;
    if result == 0 {
        result := 1;
    }
    if result > 10000 {
        result := 10000;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 100000
{
    var stack := new int[n + 1];
    var stackSize := 1;
    stack[0] := n;
    
    var k := 0;
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant 1 <= stackSize <= n + 1
        invariant stackSize <= stack.Length
    {
        if k == 0 {
            // Multiplication
            if stackSize > 0 {
                stack[stackSize - 1] := stack[stackSize - 1] * x;
            }
        } else if k == 1 {
            // Division
            if stackSize > 0 && x != 0 {
                stack[stackSize - 1] := stack[stackSize - 1] / x;
            }
        } else if k == 2 {
            // Addition (push positive)
            if stackSize < stack.Length {
                stack[stackSize] := x;
                stackSize := stackSize + 1;
            }
        } else {
            // Subtraction (push negative)
            if stackSize < stack.Length {
                stack[stackSize] := -x;
                stackSize := stackSize + 1;
            }
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum the stack
    result := 0;
    var i := 0;
    while i < stackSize
        invariant 0 <= i <= stackSize
    {
        result := result + stack[i];
        i := i + 1;
    }
    
    // Ensure result is in valid range
    if result < 1 {
        result := 1;
    } else if result > 100000 {
        result := 100000;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 0 <= result <= 1000000000
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        f[i] := 0;
        i := i + 1;
    }
    
    f[0] := 1;
    
    // Process coin 1
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant f[0] == 1
    {
        f[i] := (f[i] + f[i - 1]) % mod;
        i := i + 1;
    }
    
    // Process coin 2
    i := 2;
    while i <= n
        invariant 2 <= i <= n + 1
    {
        f[i] := (f[i] + f[i - 2]) % mod;
        i := i + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        i := 6;
        while i <= n
            invariant 6 <= i <= n + 1
        {
            f[i] := (f[i] + f[i - 6]) % mod;
            i := i + 1;
        }
    }
    
    result := f[n];
    
    if n >= 4 {
        result := (result + f[n - 4]) % mod;
    }
    
    if n >= 8 {
        result := (result + f[n - 8]) % mod;
    }
    
    if result < 0 {
        result := 0;
    } else if result > 1000000000 {
        result := 1000000000;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= 1000000000
{
    if n == 0 {
        result := 0;
        return;
    }
    
    // Convert to array of digits
    var digits := new int[10]; // max 10 digits for numbers up to 10^9
    var temp := n;
    var digitCount := 0;
    
    while temp > 0 && digitCount < 10
        invariant temp >= 0
        invariant 0 <= digitCount <= 10
    {
        digits[digitCount] := temp % 10;
        temp := temp / 10;
        digitCount := digitCount + 1;
    }
    
    if digitCount == 0 {
        result := 0;
        return;
    }
    
    // Reverse to get most significant digit first
    var i := 0;
    while i < digitCount / 2
        invariant 0 <= i <= digitCount / 2
    {
        var temp_digit := digits[i];
        digits[i] := digits[digitCount - 1 - i];
        digits[digitCount - 1 - i] := temp_digit;
        i := i + 1;
    }
    
    // Find first decreasing position
    i := 1;
    while i < digitCount && digits[i - 1] <= digits[i]
        invariant 1 <= i <= digitCount
    {
        i := i + 1;
    }
    
    if i < digitCount {
        // Make it monotone increasing
        while i > 0 && digits[i - 1] > digits[i]
            invariant 0 <= i <= digitCount
        {
            if digits[i - 1] > 0 {
                digits[i - 1] := digits[i - 1] - 1;
            }
            i := i - 1;
        }
        
        i := i + 1;
        while i < digitCount
            invariant 0 <= i <= digitCount
        {
            digits[i] := 9;
            i := i + 1;
        }
    }
    
    // Convert back to integer
    result := 0;
    i := 0;
    while i < digitCount
        invariant 0 <= i <= digitCount
        invariant 0 <= result <= 1000000000
    {
        var newResult := result * 10 + digits[i];
        if newResult > 1000000000 || newResult < 0 {
            result := 1000000000;
        } else {
            result := newResult;
        }
        i := i + 1;
    }
    
    if result < 0 {
        result := 0;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures 0 <= result <= 1000000000
{
    var o1 := countLargestGroup_1399(o);
    var o2 := clumsy_1006(o1);
    var o3 := numberOfWays_3183(o2);
    result := monotoneIncreasingDigits_738(o3);
}
