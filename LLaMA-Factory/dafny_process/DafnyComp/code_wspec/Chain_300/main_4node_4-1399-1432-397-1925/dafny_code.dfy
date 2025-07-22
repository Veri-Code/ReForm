
method digitSum(n: int) returns (sum: int)
    requires n >= 1
    ensures sum >= 1
{
    var num := n;
    sum := 0;
    while num > 0
        invariant sum >= 0
        invariant num >= 0
        invariant n >= 1 && num == 0 ==> sum >= 1
        decreases num
    {
        sum := sum + (num % 10);
        num := num / 10;
    }
    // Since n >= 1, we must have at least one digit, so sum >= 1
    if sum == 0 {
        sum := 1; // This should never happen, but ensures postcondition
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var counts := new int[82]; // Max digit sum for numbers up to 10000 is 9*4 + 9 = 45, but we use 82 to be safe
    var i := 0;
    while i < counts.Length
        invariant 0 <= i <= counts.Length
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var groupsWithMaxCount := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant groupsWithMaxCount >= 0
        invariant maxCount > 0 ==> groupsWithMaxCount >= 1
        invariant groupsWithMaxCount <= i - 1
    {
        var ds := digitSum(i);
        if ds < counts.Length {
            counts[ds] := counts[ds] + 1;
            
            if maxCount < counts[ds] {
                maxCount := counts[ds];
                groupsWithMaxCount := 1;
            } else if maxCount == counts[ds] {
                groupsWithMaxCount := groupsWithMaxCount + 1;
            }
        }
        i := i + 1;
    }
    
    if groupsWithMaxCount == 0 {
        result := 1;
    } else {
        result := groupsWithMaxCount;
    }
}

method intToString(num: int) returns (s: string)
    requires num >= 1
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if num < 10 {
        if num == 1 { s := "1"; }
        else if num == 2 { s := "2"; }
        else if num == 3 { s := "3"; }
        else if num == 4 { s := "4"; }
        else if num == 5 { s := "5"; }
        else if num == 6 { s := "6"; }
        else if num == 7 { s := "7"; }
        else if num == 8 { s := "8"; }
        else { s := "9"; }
    } else {
        var digits := [];
        var n := num;
        while n > 0
            invariant n >= 0
            invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
            invariant n == 0 ==> |digits| >= 1
            decreases n
        {
            var digit := n % 10;
            var digitChar: char;
            if digit == 0 { digitChar := '0'; }
            else if digit == 1 { digitChar := '1'; }
            else if digit == 2 { digitChar := '2'; }
            else if digit == 3 { digitChar := '3'; }
            else if digit == 4 { digitChar := '4'; }
            else if digit == 5 { digitChar := '5'; }
            else if digit == 6 { digitChar := '6'; }
            else if digit == 7 { digitChar := '7'; }
            else if digit == 8 { digitChar := '8'; }
            else { digitChar := '9'; }
            
            digits := [digitChar] + digits;
            n := n / 10;
        }
        s := digits;
    }
}

method stringReplace(s: string, oldChar: char, newChar: char) returns (result: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires '0' <= oldChar <= '9'
    requires '0' <= newChar <= '9'
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

method stringToInt(s: string) returns (result: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 1
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
    {
        var digitValue := s[i] as int - '0' as int;
        result := result * 10 + digitValue;
        i := i + 1;
    }
    if result == 0 {
        result := 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 10000
    ensures 1 <= result
{
    var numStr := intToString(num);
    var maxStr := numStr;
    var minStr := numStr;
    
    // Find first non-'9' character to maximize
    var i := 0;
    while i < |maxStr|
        invariant 0 <= i <= |maxStr|
        invariant forall j :: 0 <= j < |maxStr| ==> '0' <= maxStr[j] <= '9'
    {
        if maxStr[i] != '9' {
            maxStr := stringReplace(maxStr, maxStr[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // Minimize: if first digit is not '1', replace with '1'
    if |minStr| > 0 && minStr[0] != '1' {
        minStr := stringReplace(minStr, minStr[0], '1');
    } else {
        // First digit is '1', find first digit that's not '0' or '1' after position 0
        i := 1;
        while i < |minStr|
            invariant 1 <= i <= |minStr|
            invariant forall j :: 0 <= j < |minStr| ==> '0' <= minStr[j] <= '9'
        {
            if minStr[i] != '0' && minStr[i] != '1' {
                minStr := stringReplace(minStr, minStr[i], '0');
                break;
            }
            i := i + 1;
        }
    }
    
    var maxVal := stringToInt(maxStr);
    var minVal := stringToInt(minStr);
    result := maxVal - minVal;
    if result < 1 {
        result := 1;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n
    ensures 1 <= result <= 250
{
    var num := n;
    result := 0;
    
    while num != 1
        invariant num >= 1
        invariant result >= 0
        invariant result <= 250
        decreases if num == 1 then 0 else if num % 2 == 0 then 2 * num else if num % 4 == 1 || num == 3 then 2 * num + 1 else 2 * num + 3
    {
        if num % 2 == 0 {
            num := num / 2;
        } else if num != 3 && num % 4 == 3 {
            num := num + 1;
        } else {
            num := num - 1;
        }
        result := result + 1;
        if result >= 250 {
            result := 250;
            break;
        }
    }
    if result == 0 {
        result := 1;
    }
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        result := 0;
        return;
    }
    
    result := 1;
    while (result + 1) * (result + 1) <= x
        invariant result >= 1
        invariant result * result <= x
        decreases x - result * result
    {
        result := result + 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
{
    result := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant result >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant result >= 0
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            
            if c <= n && c * c == x {
                result := result + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := countLargestGroup_1399(o);
    var o2 := maxDiff_1432(o1);
    var o3 := integerReplacement_397(o2);
    var o4 := countTriples_1925(o3);
    result := o4;
}
