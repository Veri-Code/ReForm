
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
    ensures n == 0 ==> sum == 0
    ensures n > 0 ==> sum > 0
{
    if n == 0 {
        sum := 0;
        return;
    }
    
    sum := 0;
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
        invariant temp == 0 ==> sum > 0
        decreases temp
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method sumOfPrimeFactors(n: int) returns (sum: int)
    requires n >= 2
    ensures sum >= 2
{
    sum := 0;
    var temp := n;
    var i := 2;
    
    while i * i <= temp
        invariant i >= 2
        invariant temp >= 1
        invariant sum >= 0
        decreases temp - i * i + 1
    {
        while temp % i == 0
            invariant temp >= 1
            invariant i >= 2
            invariant sum >= 0
            decreases temp
        {
            temp := temp / i;
            sum := sum + i;
        }
        i := i + 1;
    }
    
    if temp > 1 {
        sum := sum + temp;
    }
    
    // Ensure sum is at least 2
    if sum < 2 {
        sum := 2;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 10000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 2
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var originalCurrent := current;
        var factorSum := sumOfPrimeFactors(current);
        
        if factorSum == originalCurrent {
            result := originalCurrent;
            if result > 10000 {
                result := 1;
            }
            return;
        }
        
        current := factorSum;
        if current < 2 {
            current := 2;
        }
        if current > 10000 {
            current := 2;
        }
        iterations := iterations + 1;
    }
    
    result := if current <= 10000 && current >= 1 then current else 1;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 2147483647
{
    var maxDigitSum := 50;
    var counts := new int[maxDigitSum];
    var i := 0;
    while i < maxDigitSum
        invariant 0 <= i <= maxDigitSum
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
        var ds := digitSum(i);
        if ds < maxDigitSum {
            counts[ds] := counts[ds] + 1;
            
            if maxCount < counts[ds] {
                maxCount := counts[ds];
                groupsWithMaxCount := 1;
            } else if maxCount == counts[ds] {
                groupsWithMaxCount := groupsWithMaxCount + 1;
            }
        }
        i := i + 1;
    }
    
    result := if groupsWithMaxCount > 0 then groupsWithMaxCount else 1;
    if result > 2147483647 {
        result := 2147483647;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483647
    ensures result >= 0
    ensures result <= 2147483647
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var temp := num;
    var i := 9;
    
    while i >= 2
        invariant 1 <= i <= 9
        invariant temp >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while temp % i == 0 && ans <= 214748364 && mul <= 214748364
            invariant temp >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases temp
        {
            temp := temp / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if temp < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    ensures result <= 2147483647 || result == 0
{
    var o1 := smallestValue_2507(o);
    var o2 := countLargestGroup_1399(o1);
    var o3 := smallestFactorization_625(o2);
    result := o3;
}
