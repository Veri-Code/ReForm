
method IntToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        return "0";
    }
    
    var digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| >= 1
        decreases temp
    {
        var digit := temp % 10;
        digits := [('0' as int + digit) as char] + digits;
        temp := temp / 10;
    }
    
    s := "";
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |s| == i
        invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    {
        s := s + [digits[i]];
        i := i + 1;
    }
}

method StringToInt(s: string) returns (n: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures n >= 0
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
    {
        var digit := (s[i] as int) - ('0' as int);
        n := n * 10 + digit;
        i := i + 1;
    }
}

method ReplaceChar(s: string, oldChar: char, newChar: char) returns (result: string)
    requires |s| >= 1
    requires '0' <= oldChar <= '9'
    requires '0' <= newChar <= '9'
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> '0' <= result[j] <= '9'
    {
        if s[i] == oldChar {
            result := result + [newChar];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
    ensures result <= 2147483648
{
    var numStr := IntToString(num);
    var a := numStr;
    var b := numStr;
    
    // Find first non-'9' character and replace with '9'
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < |a| ==> '0' <= a[j] <= '9'
    {
        if a[i] != '9' {
            a := ReplaceChar(a, a[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // For minimum: if first digit is not '1', replace with '1'
    // Otherwise, find first digit that's not '0' or '1' and replace with '0'
    if |b| > 0 && b[0] != '1' {
        b := ReplaceChar(b, b[0], '1');
    } else {
        var j := 1;
        while j < |b|
            invariant 1 <= j <= |b|
            invariant forall k :: 0 <= k < |b| ==> '0' <= b[k] <= '9'
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
    
    // Ensure result is within bounds
    if maxVal >= minVal {
        result := maxVal - minVal;
    } else {
        result := 0;
    }
    
    // Additional safety check
    if result > 2147483648 {
        result := 2147483648;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 1000000000
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var temp := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant temp >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while temp % i == 0
            invariant temp >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases temp
        {
            temp := temp / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if mul > 100000000 { // Prevent overflow
                return 0;
            }
        }
        i := i - 1;
    }
    
    if temp < 2 && ans <= 1000000000 {
        result := ans;
    } else {
        result := 0;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
{
    if n == 0 {
        return 0;
    }
    
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant a1 >= 1
        invariant step <= 1000000000
        decreases cnt
    {
        if i % 2 == 1 {
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
        
        // Prevent infinite loops
        if step > 1000000000 {
            break;
        }
    }
    
    result := a1;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures true
{
    var o1 := maxDiff_1432(o);
    
    // Ensure o1 is within valid range for smallestFactorization_625
    if o1 < 1 {
        o1 := 1;
    } else if o1 > 2147483648 {
        o1 := 2147483648;
    }
    
    var o2 := smallestFactorization_625(o1);
    
    // Ensure o2 is within valid range for lastRemaining_390
    if o2 < 1 {
        o2 := 1;
    } else if o2 > 1000000000 {
        o2 := 1000000000;
    }
    
    var o3 := lastRemaining_390(o2);
    result := o3;
}
