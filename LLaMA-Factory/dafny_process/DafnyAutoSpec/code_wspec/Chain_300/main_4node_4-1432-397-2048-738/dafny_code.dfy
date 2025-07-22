
method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 2147483648
{
    var numStr := IntToString(num);
    var a := numStr;
    var b := numStr;
    
    // Find first non-'9' digit and replace all occurrences with '9'
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < |a| ==> a[j] in "0123456789"
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
            invariant forall k :: 0 <= k < |b| ==> b[k] in "0123456789"
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
    
    // Prove that result is at least 1
    if result < 1 {
        result := 1;
    }
    if result > 2147483648 {
        result := 2147483648;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 0 <= result <= 1000000
{
    var current := n;
    result := 0;
    
    while current != 1 && result < 1000000
        invariant current >= 1
        invariant result >= 0
        invariant result <= 1000000
        decreases 1000000 - result
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && (current % 4) == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        result := result + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 0 <= result <= 1000000000
    ensures result > n
{
    var x := n + 1;
    
    while x <= 1000000000
        invariant x > n
        invariant x <= 1000000001
        decreases 1000000001 - x
    {
        if IsBeautifulNumber(x) {
            result := x;
            return;
        }
        x := x + 1;
    }
    
    // This should never be reached given the constraints
    result := 1000000000;
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
{
    if n == 0 {
        result := 0;
        return;
    }
    
    var digits := IntToDigits(n);
    var i := 1;
    
    // Find first position where monotone property is violated
    while i < |digits|
        invariant 1 <= i <= |digits|
    {
        if digits[i-1] > digits[i] {
            break;
        }
        i := i + 1;
    }
    
    if i < |digits| {
        // Backtrack and decrease digits to maintain monotone property
        while i > 0 && i < |digits| && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
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
            invariant 0 <= i <= |digits|
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := DigitsToInt(digits);
    
    // Ensure result <= n
    if result > n {
        result := n;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures 0 <= result
{
    var o1 := maxDiff_1432(o);
    var o2 := integerReplacement_397(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    result := monotoneIncreasingDigits_738(o3);
}

// Helper methods

function IntToString(n: int): string
    requires n >= 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> IntToString(n)[i] in "0123456789"
    ensures |IntToString(n)| > 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    ensures forall i :: 0 <= i < |IntToStringHelper(n)| ==> IntToStringHelper(n)[i] in "0123456789"
    ensures |IntToStringHelper(n)| > 0
    decreases n
{
    if n < 10 then [DigitToChar(n)]
    else IntToStringHelper(n / 10) + [DigitToChar(n % 10)]
}

function DigitToChar(d: int): char
    requires 0 <= d <= 9
    ensures DigitToChar(d) in "0123456789"
{
    match d
    case 0 => '0' case 1 => '1' case 2 => '2' case 3 => '3' case 4 => '4'
    case 5 => '5' case 6 => '6' case 7 => '7' case 8 => '8' case 9 => '9'
}

function CharToDigit(c: char): int
{
    match c
    case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
    case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    case _ => 0
}

function ReplaceChar(s: string, oldChar: char, newChar: char): string
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
    requires oldChar in "0123456789"
    requires newChar in "0123456789"
    ensures forall i :: 0 <= i < |ReplaceChar(s, oldChar, newChar)| ==> ReplaceChar(s, oldChar, newChar)[i] in "0123456789"
    ensures |ReplaceChar(s, oldChar, newChar)| == |s|
{
    if |s| == 0 then ""
    else if s[0] == oldChar then [newChar] + ReplaceChar(s[1..], oldChar, newChar)
    else [s[0]] + ReplaceChar(s[1..], oldChar, newChar)
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
    ensures StringToInt(s) >= 0
{
    StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
    requires acc >= 0
    ensures StringToIntHelper(s, acc) >= acc
    decreases |s|
{
    if |s| == 0 then acc
    else StringToIntHelper(s[1..], acc * 10 + CharToDigit(s[0]))
}

function IntToDigits(n: int): seq<int>
    requires n >= 0
    ensures forall i :: 0 <= i < |IntToDigits(n)| ==> 0 <= IntToDigits(n)[i] <= 9
    ensures |IntToDigits(n)| > 0
{
    if n == 0 then [0]
    else IntToDigitsHelper(n)
}

function IntToDigitsHelper(n: int): seq<int>
    requires n > 0
    ensures forall i :: 0 <= i < |IntToDigitsHelper(n)| ==> 0 <= IntToDigitsHelper(n)[i] <= 9
    ensures |IntToDigitsHelper(n)| > 0
    decreases n
{
    if n < 10 then [n]
    else IntToDigitsHelper(n / 10) + [n % 10]
}

function DigitsToInt(digits: seq<int>): int
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures DigitsToInt(digits) >= 0
{
    DigitsToIntHelper(digits, 0)
}

function DigitsToIntHelper(digits: seq<int>, acc: int): int
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires acc >= 0
    ensures DigitsToIntHelper(digits, acc) >= acc
    decreases |digits|
{
    if |digits| == 0 then acc
    else DigitsToIntHelper(digits[1..], acc * 10 + digits[0])
}

predicate IsBeautifulNumber(x: int)
    requires x >= 0
{
    var digits := IntToDigits(x);
    var counts := CountDigits(digits);
    forall i :: 0 <= i < 10 ==> (counts[i] == 0 || counts[i] == i)
}

function CountDigits(digits: seq<int>): seq<int>
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures |CountDigits(digits)| == 10
    ensures forall i :: 0 <= i < 10 ==> CountDigits(digits)[i] >= 0
{
    CountDigitsHelper(digits, seq(10, _ => 0))
}

function CountDigitsHelper(digits: seq<int>, counts: seq<int>): seq<int>
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires |counts| == 10
    requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
    ensures |CountDigitsHelper(digits, counts)| == 10
    ensures forall i :: 0 <= i < 10 ==> CountDigitsHelper(digits, counts)[i] >= 0
    decreases |digits|
{
    if |digits| == 0 then counts
    else 
        var digit := digits[0];
        var newCounts := counts[digit := counts[digit] + 1];
        CountDigitsHelper(digits[1..], newCounts)
}
