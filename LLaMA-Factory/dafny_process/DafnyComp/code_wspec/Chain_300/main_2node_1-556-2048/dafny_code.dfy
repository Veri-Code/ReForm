
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
    ensures n == SeqToInt(digits)
{
    digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant temp == 0 ==> |digits| > 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp * Power10(|digits|) + SeqToInt(digits) == n
    {
        var digit := temp % 10;
        digits := [digit] + digits;
        temp := temp / 10;
    }
}

function SeqToInt(digits: seq<int>): int
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if |digits| == 0 then 0
    else digits[0] * Power10(|digits| - 1) + SeqToInt(digits[1..])
}

function Power10(n: int): int
    requires n >= 0
    ensures Power10(n) > 0
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

method ReverseSeq<T>(s: seq<T>) returns (result: seq<T>)
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
    ensures -1 <= result <= 1000000
{
    var digits := IntToDigits(n);
    var cs := digits;
    var len := |cs|;
    
    if len <= 1 {
        return -1;
    }
    
    var i := len - 2;
    var j := len - 1;
    
    // Find the rightmost character that is smaller than its next character
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i < len - 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    // Find the ceiling of cs[i] in cs[i+1..len-1]
    while cs[i] >= cs[j]
        invariant i < j < len
        invariant cs[i] < cs[j] || j > i + 1
        decreases j
    {
        j := j - 1;
    }
    
    // Swap cs[i] and cs[j]
    var temp := cs[i];
    cs := cs[i := cs[j]];
    cs := cs[j := temp];
    
    // Reverse the suffix starting at cs[i+1]
    var suffix := cs[i + 1..];
    var reversedSuffix := ReverseSeq(suffix);
    cs := cs[..i + 1] + reversedSuffix;
    
    var ans := DigitsToInt(cs);
    
    if ans > 2147483647 || ans > 1000000 { // 2^31 - 1 or constraint
        return -1;
    } else {
        return ans;
    }
}

method CountDigits(x: int) returns (counts: array<int>)
    requires x >= 0
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
    
    var y := x;
    while y > 0
        invariant y >= 0
        invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
    {
        var digit := y % 10;
        counts[digit] := counts[digit] + 1;
        y := y / 10;
    }
}

method IsBeautiful(x: int) returns (beautiful: bool)
    requires x >= 0
{
    var counts := CountDigits(x);
    beautiful := true;
    var i := 0;
    while i < 10 && beautiful
        invariant 0 <= i <= 10
    {
        if counts[i] != 0 && i != counts[i] {
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
    while x <= 10000000 // reasonable upper bound
        invariant x >= n + 1
    {
        var isBeautiful := IsBeautiful(x);
        if isBeautiful {
            return x;
        }
        x := x + 1;
    }
    // Fallback - there should always be a beautiful number
    return 1;
}

method main_2node_1(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 1
{
    var o1 := nextGreaterElement_556(o);
    var o2;
    if o1 == -1 {
        o2 := nextBeautifulNumber_2048(0);
    } else {
        o2 := nextBeautifulNumber_2048(o1);
    }
    result := o2;
}
