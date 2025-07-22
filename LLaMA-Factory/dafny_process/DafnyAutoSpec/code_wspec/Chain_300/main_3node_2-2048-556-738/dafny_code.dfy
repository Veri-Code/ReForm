
method DigitCount(n: int) returns (counts: array<int>)
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
    
    var y := n;
    while y > 0
        invariant y >= 0
        invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
    {
        var digit := y % 10;
        y := y / 10;
        counts[digit] := counts[digit] + 1;
    }
}

method IsBeautiful(n: int) returns (beautiful: bool)
    requires n >= 0
{
    var counts := DigitCount(n);
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
    ensures 1 <= result <= 2147483648
{
    var x := n + 1;
    while x <= 2147483648
        invariant n + 1 <= x <= 2147483649
    {
        var isBeautiful := IsBeautiful(x);
        if isBeautiful {
            result := x;
            return;
        }
        x := x + 1;
    }
    // This should never be reached given the constraints
    result := 1;
}

method IntToDigits(n: int) returns (digits: seq<int>)
    requires 1 <= n <= 2147483648
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    var temp := n;
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp == 0 ==> |result| >= 1
    {
        var digit := temp % 10;
        temp := temp / 10;
        result := [digit] + result;
    }
    
    digits := result;
}

method DigitsToInt(digits: seq<int>) returns (n: int)
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

method ReverseSeq(s: seq<int>) returns (reversed: seq<int>)
    ensures |reversed| == |s|
    ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
    reversed := [];
    var i := |s|;
    while i > 0
        invariant 0 <= i <= |s|
        invariant |reversed| == |s| - i
        invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == s[|s| - 1 - j]
    {
        i := i - 1;
        reversed := reversed + [s[i]];
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures -1 <= result <= 2147483648
{
    var digits := IntToDigits(n);
    var cs := digits;
    var len := |cs|;
    
    if len <= 1 {
        result := -1;
        return;
    }
    
    var i := len - 2;
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i < len - 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    var j := len - 1;
    while cs[i] >= cs[j]
        invariant i < j < len
        decreases j
    {
        j := j - 1;
    }
    
    // Swap cs[i] and cs[j]
    var temp := cs[i];
    cs := cs[i := cs[j]];
    cs := cs[j := temp];
    
    // Reverse cs[i+1..]
    var prefix := cs[..i+1];
    var suffix := cs[i+1..];
    var reversedSuffix := ReverseSeq(suffix);
    cs := prefix + reversedSuffix;
    
    var ans := DigitsToInt(cs);
    if ans > 2147483647 {
        result := -1;
    } else {
        result := ans;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires -1 <= n <= 2147483648
    ensures result >= 0
{
    if n <= 0 {
        result := 0;
        return;
    }
    
    var digits := IntToDigits(n);
    var s := digits;
    var len := |s|;
    
    if len == 0 {
        result := 0;
        return;
    }
    
    var i := 1;
    while i < len && s[i-1] <= s[i]
        invariant 1 <= i <= len
    {
        i := i + 1;
    }
    
    if i < len {
        while i > 0 && s[i-1] > s[i]
            invariant 0 <= i < len
            invariant |s| == len
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            if s[i-1] > 0 {
                s := s[i-1 := s[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        while i < len
            invariant 0 <= i <= len
            invariant |s| == len
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            s := s[i := 9];
            i := i + 1;
        }
    }
    
    result := DigitsToInt(s);
}

method main_3node_2(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures result >= 0
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2 := nextGreaterElement_556(o1);
    var o3 := monotoneIncreasingDigits_738(o2);
    result := o3;
}
