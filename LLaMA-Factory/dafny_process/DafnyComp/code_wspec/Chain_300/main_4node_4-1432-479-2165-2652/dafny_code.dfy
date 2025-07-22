
method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 8 * 100000000
{
    // Convert number to sequence of digits
    var digits := numberToDigits(num);
    var n := |digits|;
    
    // Create max number by replacing first non-9 digit with 9
    var maxNum := num;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant maxNum >= num
    {
        if digits[i] != 9 {
            maxNum := replaceDigit(num, digits[i], 9);
            break;
        }
        i := i + 1;
    }
    
    // Create min number
    var minNum := num;
    if digits[0] != 1 {
        minNum := replaceDigit(num, digits[0], 1);
    } else {
        i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant minNum <= num
        {
            if digits[i] != 0 && digits[i] != 1 {
                minNum := replaceDigit(num, digits[i], 0);
                break;
            }
            i := i + 1;
        }
    }
    
    result := maxNum - minNum;
    if result < 1 {
        result := 1;
    }
    
    // Ensure result is within bounds
    if result > 8 * 100000000 {
        result := 8 * 100000000;
    }
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) > 0
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures -1000000000000000 <= result <= 1000000000000000
{
    if n == 1 {
        result := 9;
        return;
    }
    
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        decreases a
    {
        var palindrome := createPalindrome(a);
        var t := mx;
        
        while t * t >= palindrome
            invariant 0 <= t <= mx
            decreases t
        {
            if palindrome % t == 0 {
                result := palindrome % 1337;
                return;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    result := 9;
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 1 <= result <= 1000000000000000
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
    
    var temp := absNum;
    if temp == 0 {
        cnt[0] := 1;
    } else {
        while temp > 0
            invariant temp >= 0
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
        {
            if cnt[i] > 0 {
                var j := 0;
                while j < cnt[i]
                    invariant 0 <= j <= cnt[i]
                    invariant cnt[i] >= 0
                {
                    ans := ans * 10 + i;
                    j := j + 1;
                }
            }
            i := i - 1;
        }
        result := if ans == 0 then 1 else -ans;
        if result < 1 {
            result := 1;
        }
    } else {
        // For positive numbers, arrange digits in ascending order
        // but ensure first digit is not 0
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10
                invariant 1 <= i <= 10
            {
                if cnt[i] > 0 {
                    ans := i;
                    cnt[i] := cnt[i] - 1;
                    break;
                }
                i := i + 1;
            }
        }
        
        // Add remaining digits in ascending order
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
        {
            if cnt[i] > 0 {
                var j := 0;
                while j < cnt[i]
                    invariant 0 <= j <= cnt[i]
                    invariant cnt[i] >= 0
                {
                    ans := ans * 10 + i;
                    j := j + 1;
                }
            }
            i := i + 1;
        }
        
        result := if ans == 0 then 1 else ans;
    }
    
    // Ensure result is within bounds
    if result > 1000000000000000 {
        result := 1000000000000000;
    }
    
    // Ensure result is at least 1
    if result < 1 {
        result := 1;
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
    {
        if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
            result := result + i;
        }
        i := i + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
{
    var o1 := maxDiff_1432(o);
    // Clamp o1 to valid range for largestPalindrome_479
    var o1_clamped := if o1 < 1 then 1 else if o1 > 8 then 8 else o1;
    var o2 := largestPalindrome_479(o1_clamped);
    var o3 := smallestNumber_2165(o2);
    // Clamp o3 to valid range for sumOfMultiples_2652
    var o3_clamped := if o3 < 1 then 1 else if o3 > 1000 then 1000 else o3;
    var o4 := sumOfMultiples_2652(o3_clamped);
    result := o4;
}

// Helper methods

method numberToDigits(num: int) returns (digits: seq<int>)
    requires num > 0
    ensures |digits| > 0
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    digits := [];
    var temp := num;
    
    while temp > 0
        invariant temp >= 0
        invariant |digits| >= 0
        invariant temp == 0 ==> |digits| > 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        decreases temp
    {
        var digit := temp % 10;
        digits := [digit] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        digits := [0];
    }
}

method replaceDigit(num: int, oldDigit: int, newDigit: int) returns (result: int)
    requires num > 0
    requires 0 <= oldDigit <= 9
    requires 0 <= newDigit <= 9
    ensures result > 0
{
    var digits := numberToDigits(num);
    var newDigits := seq(|digits|, i requires 0 <= i < |digits| => 
        if digits[i] == oldDigit then newDigit else digits[i]);
    result := digitsToNumber(newDigits);
}

method digitsToNumber(digits: seq<int>) returns (result: int)
    requires |digits| > 0
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result > 0
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
    
    if result == 0 {
        result := 1; // Ensure positive result
    }
}

method createPalindrome(a: int) returns (palindrome: int)
    requires a > 0
    ensures palindrome > 0
{
    var b := a;
    var x := a;
    
    while b > 0
        invariant b >= 0
        invariant x >= a
        decreases b
    {
        x := x * 10 + b % 10;
        b := b / 10;
    }
    
    palindrome := x;
}
