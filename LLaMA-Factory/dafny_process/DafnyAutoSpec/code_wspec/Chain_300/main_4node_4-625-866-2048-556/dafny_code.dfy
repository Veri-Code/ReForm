
method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 1 <= result <= 100000000 || result == 0
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var n := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant n >= 1
        invariant mul >= 1
        invariant ans >= 0
        invariant mul <= 1000000000
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant mul >= 1
            invariant ans >= 0
            invariant mul <= 1000000000
            decreases n
        {
            n := n / i;
            if mul <= 100000000 && ans <= 100000000 {
                ans := mul * i + ans;
                mul := mul * 10;
            } else {
                return 0;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 && ans <= 100000000 {
        return ans;
    } else {
        return 0;
    }
}

function isPrime(x: int): bool
    requires x >= 0
{
    if x < 2 then false
    else forall k :: 2 <= k < x && k * k <= x ==> x % k != 0
}

function reverse(x: int): int
    requires x >= 0
{
    if x == 0 then 0
    else reverseHelper(x, 0)
}

function reverseHelper(x: int, acc: int): int
    requires x >= 0
    requires acc >= 0
    decreases x
{
    if x == 0 then acc
    else reverseHelper(x / 10, acc * 10 + x % 10)
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 0 <= result <= 1000000
{
    var current := n;
    
    while current <= 1000000
        invariant current >= n
        decreases 1000000 - current
    {
        var rev := reverse(current);
        if rev == current && isPrime(current) {
            return current;
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    
    return 0; // fallback
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 2147483648
{
    var x := n + 1;
    
    while x <= 2147483648
        invariant x >= n + 1
        decreases 2147483648 - x
    {
        var y := x;
        var cnt := new int[10];
        var idx := 0;
        while idx < 10
            invariant 0 <= idx <= 10
        {
            cnt[idx] := 0;
            idx := idx + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            y := y / 10;
            if digit < 10 {
                cnt[digit] := cnt[digit] + 1;
            }
        }
        
        var isBeautiful := true;
        var i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && cnt[i] != i {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            return x;
        }
        
        x := x + 1;
    }
    
    return 1; // fallback
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= -1
{
    var digits := new int[11]; // max digits for 2^31 + 1 for safety
    var numDigits := 0;
    var temp := n;
    
    // Convert to digits array
    while temp > 0
        invariant temp >= 0
        invariant numDigits >= 0
        invariant numDigits <= digits.Length
        decreases temp
    {
        if numDigits < digits.Length {
            digits[numDigits] := temp % 10;
            numDigits := numDigits + 1;
        }
        temp := temp / 10;
    }
    
    if numDigits == 0 {
        return -1;
    }
    
    // Reverse to get most significant digit first
    var i := 0;
    while i < numDigits / 2
        invariant 0 <= i <= numDigits / 2
        invariant numDigits <= digits.Length
    {
        var temp_digit := digits[i];
        digits[i] := digits[numDigits - 1 - i];
        digits[numDigits - 1 - i] := temp_digit;
        i := i + 1;
    }
    
    // Find rightmost character that is smaller than next character
    var pivot := numDigits - 2;
    while pivot >= 0 && pivot + 1 < numDigits && digits[pivot] >= digits[pivot + 1]
        invariant -1 <= pivot < numDigits - 1
        invariant numDigits <= digits.Length
        decreases pivot + 1
    {
        pivot := pivot - 1;
    }
    
    if pivot < 0 {
        return -1;
    }
    
    // Find rightmost character that is greater than pivot
    var successor := numDigits - 1;
    while successor > pivot && digits[pivot] >= digits[successor]
        invariant pivot < successor < numDigits
        invariant numDigits <= digits.Length
        decreases successor
    {
        successor := successor - 1;
    }
    
    // Swap pivot and successor
    var temp_swap := digits[pivot];
    digits[pivot] := digits[successor];
    digits[successor] := temp_swap;
    
    // Reverse suffix
    var left := pivot + 1;
    var right := numDigits - 1;
    while left < right
        invariant pivot + 1 <= left <= right + 1 <= numDigits
        invariant numDigits <= digits.Length
        decreases right - left
    {
        var temp_rev := digits[left];
        digits[left] := digits[right];
        digits[right] := temp_rev;
        left := left + 1;
        right := right - 1;
    }
    
    // Convert back to integer
    var ans := 0;
    var j := 0;
    while j < numDigits
        invariant 0 <= j <= numDigits
        invariant ans >= 0
        decreases numDigits - j
    {
        if ans <= 214748364 {
            var newAns := ans * 10 + digits[j];
            if newAns >= 0 {
                ans := newAns;
            } else {
                return -1;
            }
        } else {
            return -1;
        }
        j := j + 1;
    }
    
    if ans > 2147483647 {
        return -1;
    } else {
        return ans;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= -1
{
    var o1 := smallestFactorization_625(o);
    if o1 == 0 {
        return -1;
    }
    var o2 := primePalindrome_866(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    var o4 := nextGreaterElement_556(o3);
    return o4;
}
