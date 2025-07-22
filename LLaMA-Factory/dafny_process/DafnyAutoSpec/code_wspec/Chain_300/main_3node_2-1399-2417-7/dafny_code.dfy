
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

method countDigits(n: int) returns (count: int)
    requires n > 0
    ensures count > 0
{
    var temp := n;
    count := 0;
    while temp > 0
        invariant temp >= 0
        invariant count >= 0
        invariant n > 0 ==> (temp == 0 ==> count > 0)
    {
        count := count + 1;
        temp := temp / 10;
    }
}

method countOddEvenDigits(n: int) returns (odd: int, even: int)
    requires n > 0
    ensures odd >= 0 && even >= 0
    ensures odd + even > 0
{
    var temp := n;
    odd := 0;
    even := 0;
    while temp > 0
        invariant temp >= 0
        invariant odd >= 0 && even >= 0
        invariant n > 0 ==> (temp == 0 ==> odd + even > 0)
    {
        var digit := temp % 10;
        if digit % 2 == 1 {
            odd := odd + 1;
        } else {
            even := even + 1;
        }
        temp := temp / 10;
    }
}

method power10(exp: int) returns (result: int)
    requires exp >= 0
    ensures result > 0
{
    result := 1;
    var i := 0;
    while i < exp
        invariant 0 <= i <= exp
        invariant result > 0
    {
        result := result * 10;
        i := i + 1;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    // Use arrays to simulate Counter behavior
    var digitSumCounts := new int[82]; // max digit sum for numbers up to 10000 is 9*4 + 9 = 45, but we use 82 for safety
    var i := 0;
    while i < digitSumCounts.Length
        invariant 0 <= i <= digitSumCounts.Length
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
        var sum := digitSum(i);
        if sum < digitSumCounts.Length {
            digitSumCounts[sum] := digitSumCounts[sum] + 1;
            
            if maxCount < digitSumCounts[sum] {
                maxCount := digitSumCounts[sum];
                groupsWithMaxCount := 1;
            } else if maxCount == digitSumCounts[sum] {
                groupsWithMaxCount := groupsWithMaxCount + 1;
            }
        }
        i := i + 1;
    }
    
    result := if groupsWithMaxCount > 0 then groupsWithMaxCount else 1;
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    decreases 1000000000 - n
{
    var odd, even := countOddEvenDigits(n);
    var totalDigits := odd + even;
    
    if totalDigits % 2 == 1 {
        // Odd number of digits, need to go to next even-digit number
        var nextPower := power10(totalDigits);
        var halfDigits := totalDigits / 2;
        var onesCount := 0;
        var i := 0;
        while i < halfDigits
            invariant 0 <= i <= halfDigits
            invariant onesCount >= 0
        {
            onesCount := onesCount * 10 + 1;
            i := i + 1;
        }
        result := nextPower + (if halfDigits > 0 then onesCount else 0);
    } else if odd == even {
        result := n;
    } else {
        // Recursive call - find next fair number
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := n; // fallback to avoid infinite recursion
        }
    }
}

method reverse_7(x: int) returns (result: int)
    requires true
    ensures true
{
    if x < -2147483648 || x > 2147483647 {
        result := 0;
        return;
    }
    
    var ans := 0;
    var temp := x;
    var mi := -2147483648;
    var mx := 2147483647;
    
    while temp != 0
    {
        // Check for overflow before multiplication
        if ans < mi / 10 + 1 || ans > mx / 10 {
            result := 0;
            return;
        }
        
        var digit := temp % 10;
        if temp < 0 && digit > 0 {
            digit := digit - 10;
        }
        
        // Additional overflow check
        if (ans > 0 && ans > (mx - digit) / 10) || (ans < 0 && ans < (mi - digit) / 10) {
            result := 0;
            return;
        }
        
        ans := ans * 10 + digit;
        temp := (temp - digit) / 10;
    }
    
    result := ans;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures true
{
    var o1 := countLargestGroup_1399(o);
    if o1 <= 1000000000 {
        var o2 := closestFair_2417(o1);
        result := reverse_7(o2);
    } else {
        result := 0;
    }
}
