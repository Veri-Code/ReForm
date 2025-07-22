
method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 999999999
{
    var numStr := IntToString(num);
    var a := numStr;
    var b := numStr;
    
    // Maximize a by replacing first non-9 digit with 9
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant IsDigitString(a)
        invariant IsDigitString(b)
    {
        if a[i] != '9' {
            a := ReplaceChar(a, a[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // Minimize b
    if |b| > 0 && b[0] != '1' {
        b := ReplaceChar(b, b[0], '1');
    } else if |b| > 1 {
        var j := 1;
        while j < |b|
            invariant 1 <= j <= |b|
            invariant IsDigitString(b)
        {
            if b[j] != '0' && b[j] != '1' {
                b := ReplaceChar(b, b[j], '0');
                break;
            }
            j := j + 1;
        }
    }
    
    var aVal := StringToInt(a);
    var bVal := StringToInt(b);
    result := aVal - bVal;
    
    if result <= 0 {
        result := 1;
    }
    
    // Ensure upper bound
    if result > 999999999 {
        result := 999999999;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures -2147483648 <= result <= 2147483648
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var product := top * x;
            if product > 2147483648 {
                product := 2147483648;
            } else if product < -2147483648 {
                product := -2147483648;
            }
            stk := stk[..|stk| - 1] + [product];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top / x];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := Sum(stk);
    if result > 2147483648 {
        result := 2147483648;
    } else if result < -2147483648 {
        result := -2147483648;
    }
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= result <= 2147483647
{
    var ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var temp := x;
    
    while temp != 0
        invariant -2147483648 <= ans <= 2147483647
        decreases if temp >= 0 then temp else -temp
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            result := 0;
            return;
        }
        
        var y := temp % 10;
        if temp < 0 && y > 0 {
            y := y - 10;
        }
        
        var newAns := ans * 10 + y;
        if newAns < -2147483648 || newAns > 2147483647 {
            result := 0;
            return;
        }
        
        ans := newAns;
        temp := (temp - y) / 10;
    }
    
    if ans < 0 {
        result := 0;
    } else {
        result := ans;
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483647
    ensures -1 <= result <= 2147483647
{
    var cs := IntToDigits(n);
    var len := |cs|;
    
    if len == 0 {
        result := -1;
        return;
    }
    
    var i := len - 2;
    
    // Find the rightmost digit that is smaller than the digit next to it
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i < len - 1
        invariant ValidDigitSeq(cs)
        decreases i + 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    // Find the smallest digit on right side of above character that is greater than cs[i]
    var j := len - 1;
    while cs[i] >= cs[j]
        invariant i < j < len
        invariant ValidDigitSeq(cs)
        decreases j - i
    {
        j := j - 1;
    }
    
    // Swap
    cs := cs[..i] + [cs[j]] + cs[i+1..j] + [cs[i]] + cs[j+1..];
    
    // Reverse the substring after position i
    cs := cs[..i+1] + Reverse(cs[i+1..]);
    
    // Ensure ValidDigitSeq is maintained
    assert ValidDigitSeq(cs);
    
    var ans := DigitsToInt(cs);
    if ans > 2147483647 {
        result := -1;
    } else {
        result := ans;
    }
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var m := Sqrt(n);
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 10001; // Large value representing infinity
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
                f[i, j] := Min(f[i, j], f[i, j - i * i] + 1);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result <= 0 || result > 10000 {
        result := 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 1
{
    var o1 := maxDiff_1432(o);
    
    if o1 > 10000 {
        result := 1;
        return;
    }
    
    var o2 := clumsy_1006(o1);
    var o3 := reverse_7(o2);
    
    if o3 == 0 {
        result := 1;
        return;
    }
    
    var o4 := nextGreaterElement_556(o3);
    
    if o4 == -1 || o4 > 10000 || o4 < 1 {
        result := 1;
        return;
    }
    
    var o5 := numSquares_279(o4);
    result := o5;
}

// Helper functions
function IntToString(n: int): string
    requires n >= 0
    ensures IsDigitString(IntToString(n))
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    ensures IsDigitString(IntToStringHelper(n))
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

predicate IsDigitString(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
    requires IsDigitString(s)
{
    StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then acc
    else StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function ReplaceChar(s: string, oldChar: char, newChar: char): string
    requires IsDigitString(s)
    requires '0' <= newChar <= '9'
    ensures IsDigitString(ReplaceChar(s, oldChar, newChar))
{
    if |s| == 0 then ""
    else if s[0] == oldChar then [newChar] + ReplaceCharHelper(s[1..], oldChar, newChar)
    else [s[0]] + ReplaceCharHelper(s[1..], oldChar, newChar)
}

function ReplaceCharHelper(s: string, oldChar: char, newChar: char): string
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires '0' <= newChar <= '9'
    ensures forall i :: 0 <= i < |ReplaceCharHelper(s, oldChar, newChar)| ==> '0' <= ReplaceCharHelper(s, oldChar, newChar)[i] <= '9'
{
    if |s| == 0 then ""
    else if s[0] == oldChar then [newChar] + ReplaceCharHelper(s[1..], oldChar, newChar)
    else [s[0]] + ReplaceCharHelper(s[1..], oldChar, newChar)
}

function Sum(arr: seq<int>): int
{
    if |arr| == 0 then 0
    else if |arr| == 1 then arr[0]
    else arr[0] + Sum(arr[1..])
}

function IntToDigits(n: int): seq<int>
    requires n >= 0
    ensures ValidDigitSeq(IntToDigits(n))
{
    if n == 0 then [0]
    else IntToDigitsHelper(n)
}

function IntToDigitsHelper(n: int): seq<int>
    requires n > 0
    ensures ValidDigitSeq(IntToDigitsHelper(n))
    decreases n
{
    if n < 10 then [n]
    else IntToDigitsHelper(n / 10) + [n % 10]
}

predicate ValidDigitSeq(digits: seq<int>)
{
    forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
}

function DigitsToInt(digits: seq<int>): int
    requires ValidDigitSeq(digits)
    ensures DigitsToInt(digits) >= 0
{
    DigitsToIntHelper(digits, 0)
}

function DigitsToIntHelper(digits: seq<int>, acc: int): int
    requires ValidDigitSeq(digits)
    requires acc >= 0
    ensures DigitsToIntHelper(digits, acc) >= 0
    decreases |digits|
{
    if |digits| == 0 then acc
    else DigitsToIntHelper(digits[1..], acc * 10 + digits[0])
}

function Reverse<T>(s: seq<T>): seq<T>
    ensures |Reverse(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> Reverse(s)[i] == s[|s| - 1 - i]
{
    if |s| <= 1 then s
    else Reverse(s[1..]) + [s[0]]
}

lemma ReversePreservesValidDigitSeq(s: seq<int>)
    requires ValidDigitSeq(s)
    ensures ValidDigitSeq(Reverse(s))
{
    if |s| <= 1 {
        // Base case
    } else {
        ReversePreservesValidDigitSeq(s[1..]);
    }
}

function Sqrt(n: int): int
    requires n >= 0
    ensures Sqrt(n) >= 0
    ensures Sqrt(n) * Sqrt(n) <= n
    ensures n < (Sqrt(n) + 1) * (Sqrt(n) + 1)
{
    SqrtHelper(n, 0, n + 1)
}

function SqrtHelper(n: int, low: int, high: int): int
    requires 0 <= low < high
    requires low * low <= n < high * high
    ensures low <= SqrtHelper(n, low, high) < high
    ensures SqrtHelper(n, low, high) * SqrtHelper(n, low, high) <= n
    ensures n < (SqrtHelper(n, low, high) + 1) * (SqrtHelper(n, low, high) + 1)
    decreases high - low
{
    if high - low <= 1 then low
    else
        var mid := (low + high) / 2;
        if mid * mid <= n then SqrtHelper(n, mid, high)
        else SqrtHelper(n, low, mid)
}

function Min(a: int, b: int): int
{
    if a <= b then a else b
}
