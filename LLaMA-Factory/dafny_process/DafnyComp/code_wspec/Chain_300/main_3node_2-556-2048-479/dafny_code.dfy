
method DigitsToInt(digits: seq<int>) returns (result: int)
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires |digits| > 0
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

method IntToDigits(n: int) returns (digits: seq<int>)
    requires n > 0
    ensures |digits| > 0
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp == 0 ==> |digits| > 0
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
}

method ReverseSequence(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
{
    result := [];
    var i := |s|;
    while i > 0
        invariant 0 <= i <= |s|
        invariant |result| == |s| - i
        invariant forall j :: 0 <= j < |result| ==> result[j] == s[|s| - 1 - j]
    {
        i := i - 1;
        result := result + [s[i]];
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= -1
{
    var digits := IntToDigits(n);
    var len := |digits|;
    
    if len <= 1 {
        return -1;
    }
    
    var i := len - 2;
    
    // Find the rightmost digit that is smaller than the digit next to it
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len - 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    var j := len - 1;
    
    // Find the smallest digit on right side of above character that is greater than digits[i]
    while digits[i] >= digits[j]
        invariant i < j < len
        decreases j
    {
        j := j - 1;
    }
    
    // Swap the found characters
    var temp := digits[i];
    var newDigits := digits[i := digits[j]][j := temp];
    
    // Reverse the sequence after position i
    var leftPart := newDigits[..i+1];
    var rightPart := newDigits[i+1..];
    var reversedRight := ReverseSequence(rightPart);
    var finalDigits := leftPart + reversedRight;
    
    var ans := DigitsToInt(finalDigits);
    
    if ans > 2147483647 {
        return -1;
    } else {
        return ans;
    }
}

method CountDigits(n: int) returns (counts: array<int>)
    requires n >= 0
    ensures counts.Length == 10
    ensures forall i :: 0 <= i < 10 ==> counts[i] >= 0
{
    counts := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
    {
        var digit := temp % 10;
        counts[digit] := counts[digit] + 1;
        temp := temp / 10;
    }
}

method IsBeautiful(n: int) returns (beautiful: bool)
    requires n > 0
{
    var counts := CountDigits(n);
    beautiful := true;
    var i := 0;
    while i < 10 && beautiful
        invariant 0 <= i <= 10
    {
        if counts[i] != 0 && counts[i] != i {
            beautiful := false;
        }
        i := i + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result >= 1
{
    var x := n + 1;
    while x <= 10000000  // Upper bound to ensure termination
        invariant x >= n + 1
    {
        var isBeaut := IsBeautiful(x);
        if isBeaut {
            return x;
        }
        x := x + 1;
    }
    return 1;  // Fallback, should not reach here for valid inputs
}

function Power(base: int, exp: int): int
    requires base >= 0 && exp >= 0
    ensures Power(base, exp) >= 0
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}

method CreatePalindrome(a: int) returns (palindrome: int)
    requires a > 0
    ensures palindrome >= 0
{
    palindrome := a;
    var b := a;
    while b > 0
        invariant b >= 0
        invariant palindrome >= 0
    {
        palindrome := palindrome * 10 + (b % 10);
        b := b / 10;
    }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures result >= 0
{
    if n == 1 {
        return 9;
    }
    
    var mx := Power(10, n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant a >= mx / 10
        invariant a <= mx
        decreases a
    {
        var x := CreatePalindrome(a);
        var t := mx;
        
        while t * t >= x && t > 0
            invariant t >= 0
        {
            if x % t == 0 {
                return x % 1337;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := nextGreaterElement_556(o);
    if o1 == -1 {
        result := 9;  // Default case when no next greater element exists
        return;
    }
    
    // Ensure o1 is within bounds for nextBeautifulNumber_2048
    if o1 > 1000000 {
        result := 9;
        return;
    }
    
    var o2 := nextBeautifulNumber_2048(o1);
    
    // Ensure o2 is within bounds for largestPalindrome_479
    if o2 > 8 {
        result := 9;
        return;
    }
    
    var o3 := largestPalindrome_479(o2);
    result := o3;
}
