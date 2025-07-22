
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant sum >= 0
        invariant temp >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var cnt := new int[82]; // max digit sum for numbers up to 10000 is 9*4 = 36, but we use 82 for safety
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    var ans := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
    {
        var s := digitSum(i);
        if s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    if ans == 0 {
        result := 1;
    } else {
        result := ans;
    }
}

method isPrime(x: int) returns (prime: bool)
    requires x >= 0
{
    if x < 2 {
        prime := false;
        return;
    }
    
    var v := 2;
    prime := true;
    
    while v * v <= x && prime
        invariant v >= 2
        invariant prime ==> (forall k :: 2 <= k < v ==> x % k != 0)
    {
        if x % v == 0 {
            prime := false;
        }
        v := v + 1;
    }
}

method reverseNumber(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    var temp := x;
    res := 0;
    
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
    {
        res := res * 10 + (temp % 10);
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= n
    ensures result <= 2147483647
{
    var current := n;
    
    while current <= 2147483647
        invariant current >= n
        decreases 2147483647 - current
    {
        var rev := reverseNumber(current);
        var isPalin := (rev == current);
        var isPrim := isPrime(current);
        
        if isPalin && isPrim {
            result := current;
            return;
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    
    // Fallback - should not reach here given constraints
    result := 2147483647;
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
    
    while i > 1
        invariant 1 <= i <= 9
        invariant temp >= 1
        invariant mul >= 1
        invariant ans >= 0
        decreases i
    {
        while temp % i == 0
            invariant temp >= 1
            invariant mul >= 1
            invariant ans >= 0
            decreases temp
        {
            temp := temp / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if mul > 214748364 { // Prevent overflow
                result := 0;
                return;
            }
        }
        i := i - 1;
    }
    
    if temp < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        digits := [0];
        return;
    }
    
    var temp := n;
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp == 0 ==> |result| >= 1
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    digits := result;
}

method digitsToInt(digits: seq<int>) returns (n: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures n >= 0
{
    n := 0;
    var i := 0;
    
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant n >= 0
    {
        n := n * 10 + digits[i];
        i := i + 1;
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483647
    ensures result >= -1
    ensures result <= 2147483647
{
    var digits := intToDigits(n);
    var len := |digits|;
    
    if len <= 1 {
        result := -1;
        return;
    }
    
    var i := len - 2;
    
    // Find the rightmost digit that is smaller than the digit next to it
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len - 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    // Find the smallest digit on right side of above character that is greater than digits[i]
    var j := len - 1;
    while digits[i] >= digits[j]
        invariant i < j < len
        decreases j
    {
        j := j - 1;
    }
    
    // Swap digits[i] and digits[j]
    var newDigits := digits[i := digits[j]][j := digits[i]];
    
    // Reverse the sequence after position i
    var left := i + 1;
    var right := len - 1;
    
    while left < right
        invariant i + 1 <= left <= right + 1 <= len
        invariant |newDigits| == len
        invariant forall k :: 0 <= k < |newDigits| ==> 0 <= newDigits[k] <= 9
    {
        var temp := newDigits[left];
        newDigits := newDigits[left := newDigits[right]];
        newDigits := newDigits[right := temp];
        left := left + 1;
        right := right - 1;
    }
    
    var ans := digitsToInt(newDigits);
    
    if ans > 2147483647 {
        result := -1;
    } else {
        result := ans;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= -1
    ensures result <= 2147483647
{
    var o1 := countLargestGroup_1399(o);
    assert o1 >= 1;
    
    // Since o1 can be large, we need to handle the case where it exceeds the bound
    if o1 > 100000000 {
        result := -1;
        return;
    }
    
    var o2 := primePalindrome_866(o1);
    assert o2 <= 2147483647;
    
    var o3 := smallestFactorization_625(o2);
    assert o3 >= 0 && o3 <= 2147483647;
    
    if o3 == 0 {
        result := -1;
        return;
    }
    
    var o4 := nextGreaterElement_556(o3);
    result := o4;
}
