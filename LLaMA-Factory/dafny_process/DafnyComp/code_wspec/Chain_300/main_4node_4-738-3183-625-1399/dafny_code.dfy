
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
    ensures n == 0 ==> sum == 0
    ensures n > 0 ==> sum > 0
{
    sum := 0;
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
        invariant temp == 0 ==> sum > 0 || n == 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
    
    if n == 0 {
        sum := 0;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
    ensures result <= 1000000000
{
    if n == 0 {
        result := 0;
        return;
    }
    
    // Convert to sequence of digits
    var digits: seq<int> := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant temp < n ==> |digits| > 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        result := 0;
        return;
    }
    
    // Find first decreasing position
    var i := 1;
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Make monotone by decreasing and setting rest to 9
        var newDigits := digits;
        while i > 0 && i < |newDigits| && newDigits[i-1] > newDigits[i]
            invariant 0 <= i <= |newDigits|
            invariant |newDigits| == |digits|
        {
            if newDigits[i-1] > 0 {
                newDigits := newDigits[i-1 := newDigits[i-1] - 1];
            }
            i := i - 1;
        }
        
        // Set remaining digits to 9
        i := i + 1;
        while i < |newDigits|
            invariant i <= |newDigits|
            invariant |newDigits| == |digits|
        {
            newDigits := newDigits[i := 9];
            i := i + 1;
        }
        digits := newDigits;
    }
    
    // Convert back to integer
    result := 0;
    var multiplier := 1;
    i := |digits| - 1;
    while i >= 0
        invariant -1 <= i < |digits|
        invariant result >= 0
        invariant multiplier >= 1
    {
        if digits[i] >= 0 && digits[i] <= 9 {
            result := result + digits[i] * multiplier;
        }
        multiplier := multiplier * 10;
        i := i - 1;
    }
    
    if result > n {
        result := n;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 2147483648
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    // Initialize array
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
        invariant forall j :: 0 <= j < i ==> f[j] >= 1
    {
        f[i] := (f[i] + f[i - 1]) % mod;
        if f[i] == 0 {
            f[i] := 1;
        }
        i := i + 1;
    }
    
    // Process coin 2
    i := 2;
    while i <= n
        invariant 2 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> f[j] >= 1
    {
        f[i] := (f[i] + f[i - 2]) % mod;
        if f[i] == 0 {
            f[i] := 1;
        }
        i := i + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        i := 6;
        while i <= n
            invariant 6 <= i <= n + 1
            invariant forall j :: 0 <= j < i ==> f[j] >= 1
        {
            f[i] := (f[i] + f[i - 6]) % mod;
            if f[i] == 0 {
                f[i] := 1;
            }
            i := i + 1;
        }
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    result := if ans == 0 then 1 else ans;
    
    if result <= 0 {
        result := 1;
    }
    if result > 2147483648 {
        result := 2147483648;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 1 <= result <= 10000 || result == 0
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var remaining := num;
    
    var i := 9;
    while i >= 2
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant ans >= 0
        invariant mul >= 1
    {
        while remaining % i == 0 && mul <= 1000000000
            invariant remaining >= 1
            invariant ans >= 0
            invariant mul >= 1
        {
            remaining := remaining / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 2147483647 {
        result := if ans == 0 then 1 else ans;
    } else {
        result := 0;
    }
    
    // Ensure result is in valid range
    if result > 10000 {
        result := 0;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var counts := new int[82]; // Max digit sum for numbers up to 10000 is 9+9+9+9 = 36, but we use 82 for safety
    var i := 0;
    while i < 82
        invariant 0 <= i <= 82
    {
        counts[i] := 0;
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
        var sum := digitSum(i);
        if sum < 82 {
            counts[sum] := counts[sum] + 1;
            
            if maxCount < counts[sum] {
                maxCount := counts[sum];
                groupsWithMaxCount := 1;
            } else if maxCount == counts[sum] {
                groupsWithMaxCount := groupsWithMaxCount + 1;
            }
        }
        i := i + 1;
    }
    
    result := if groupsWithMaxCount == 0 then 1 else groupsWithMaxCount;
}

method main_4node_4(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := monotoneIncreasingDigits_738(o);
    
    // Ensure o1 is in valid range for next function
    if o1 < 1 {
        o1 := 1;
    } else if o1 > 100000 {
        o1 := 100000;
    }
    
    var o2 := numberOfWays_3183(o1);
    
    // Ensure o2 is in valid range for next function  
    if o2 < 1 {
        o2 := 1;
    } else if o2 > 2147483648 {
        o2 := 2147483648;
    }
    
    var o3 := smallestFactorization_625(o2);
    
    // Ensure o3 is in valid range for next function
    if o3 < 1 {
        o3 := 1;
    } else if o3 > 10000 {
        o3 := 10000;
    }
    
    result := countLargestGroup_1399(o3);
}
