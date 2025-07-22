
method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
    ensures result <= n || n == 0
{
    if n == 0 {
        return 1;
    }
    
    var digits := intToDigits(n);
    var i := 1;
    
    // Find first position where monotone property is violated
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
        invariant forall j :: 0 <= j < i-1 ==> digits[j] <= digits[j+1]
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Fix the violation by decrementing and propagating
        while i > 0 && i < |digits| && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            invariant |digits| > 0
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        
        // Set all following digits to 9
        i := i + 1;
        while i < |digits|
            invariant i <= |digits|
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(digits);
    if result == 0 {
        result := 1;
    } else if result > 1000000000 {
        result := 1000000000;
    }
    
    // Ensure result <= n
    if result > n {
        result := n;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
    decreases 1000000000 - n
{
    var evenCount, oddCount, digitCount := countDigits(n);
    
    if digitCount % 2 == 1 {
        // Odd number of digits - need even number for fair number
        var nextPowerOf10 := power10(digitCount);
        var halfDigits := digitCount / 2;
        var onesCount := if halfDigits > 0 then power10(halfDigits) - 1 else 0;
        result := nextPowerOf10 + onesCount;
        if result > 1000000000 {
            result := 1000000000;
        }
    } else if evenCount == oddCount {
        result := n;
    } else {
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 1000000000;
        }
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result >= 0
        invariant result == sumMultiplesUpTo(i - 1)
    {
        if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
            result := result + i;
        }
        i := i + 1;
    }
}

function sumMultiplesUpTo(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n % 3 == 0 || n % 5 == 0 || n % 7 == 0 then
        n + sumMultiplesUpTo(n - 1)
    else
        sumMultiplesUpTo(n - 1)
}

method main_3node_2(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures 0 <= result
{
    var o1 := monotoneIncreasingDigits_738(o);
    var o2 := closestFair_2417(o1);
    if o2 <= 1000 {
        var o3 := sumOfMultiples_2652(o2);
        result := o3;
    } else {
        result := 0;
    }
}

// Helper methods for digit manipulation
method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| > 0
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        return [0];
    }
    
    digits := [];
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| > 0
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
}

method digitsToInt(digits: seq<int>) returns (result: int)
    requires |digits| > 0
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

method countDigits(n: int) returns (evenCount: int, oddCount: int, digitCount: int)
    requires n > 0
    ensures evenCount >= 0 && oddCount >= 0 && digitCount > 0
    ensures evenCount + oddCount == digitCount
{
    evenCount := 0;
    oddCount := 0;
    digitCount := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant evenCount >= 0 && oddCount >= 0 && digitCount >= 0
        invariant evenCount + oddCount == digitCount
        invariant temp > 0 ==> digitCount >= 0
        invariant temp == 0 ==> digitCount > 0
    {
        var digit := temp % 10;
        if digit % 2 == 0 {
            evenCount := evenCount + 1;
        } else {
            oddCount := oddCount + 1;
        }
        digitCount := digitCount + 1;
        temp := temp / 10;
    }
}

function power10(n: int): int
    requires n >= 0
    ensures power10(n) > 0
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}
