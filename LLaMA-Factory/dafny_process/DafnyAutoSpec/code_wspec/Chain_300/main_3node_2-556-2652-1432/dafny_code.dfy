
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
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
}

method ReverseSeq(s: seq<int>) returns (result: seq<int>)
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
    var cs := IntToDigits(n);
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
    
    if ans > 2147483647 {
        return -1;
    } else {
        return ans;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    var x := 1;
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method ReplaceChar(s: string, oldChar: char, newChar: char) returns (result: string)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> result[i] == newChar) && (s[i] != oldChar ==> result[i] == s[i])
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == oldChar ==> result[j] == newChar) && (s[j] != oldChar ==> result[j] == s[j])
    {
        if s[i] == oldChar {
            result := result + [newChar];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

method IntToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| > 0
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        return "0";
    }
    
    s := "";
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
        invariant temp == 0 ==> |s| > 0
        decreases temp
    {
        var digit := temp % 10;
        var digitChar := (digit as char) + '0';
        s := [digitChar] + s;
        temp := temp / 10;
    }
}

method StringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
    {
        var digit := (s[i] as int) - ('0' as int);
        result := result * 10 + digit;
        i := i + 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
{
    var a := IntToString(num);
    var b := IntToString(num);
    
    // Maximize: replace first non-'9' with '9'
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
    {
        if a[i] != '9' {
            a := ReplaceChar(a, a[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // Minimize: replace appropriately
    if |b| > 0 && b[0] != '1' {
        b := ReplaceChar(b, b[0], '1');
    } else {
        var j := 1;
        while j < |b|
            invariant 1 <= j <= |b|
        {
            if b[j] != '0' && b[j] != '1' {
                b := ReplaceChar(b, b[j], '0');
                break;
            }
            j := j + 1;
        }
    }
    
    var maxVal := StringToInt(a);
    var minVal := StringToInt(b);
    result := maxVal - minVal;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := nextGreaterElement_556(o);
    if o1 == -1 {
        result := 0;
        return;
    }
    
    // Ensure o1 is in valid range for sumOfMultiples_2652
    if o1 < 1 || o1 > 1000 {
        result := 0;
        return;
    }
    
    var o2 := sumOfMultiples_2652(o1);
    
    // Ensure o2 is in valid range for maxDiff_1432
    if o2 < 1 || o2 > 100000000 {
        result := 0;
        return;
    }
    
    var o3 := maxDiff_1432(o2);
    result := if o3 >= 0 then o3 else 0;
}
