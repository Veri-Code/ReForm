
function digitToInt(c: char): int
    requires '0' <= c <= '9'
    ensures 0 <= digitToInt(c) <= 9
    ensures digitToInt(c) == (c as int) - ('0' as int)
{
    (c as int) - ('0' as int)
}

function intToChar(n: int): char
    requires 0 <= n <= 9
    ensures '0' <= intToChar(n) <= '9'
    ensures intToChar(n) == (('0' as int) + n) as char
{
    (('0' as int) + n) as char
}

method stringToInt(s: seq<char>) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
    {
        var digit := digitToInt(s[i]);
        res := res * 10 + digit;
        i := i + 1;
    }
    return res;
}

method intToString(n: int) returns (result: seq<char>)
    requires n >= 0
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
    if n == 0 {
        return ['0'];
    }
    
    var digits: seq<char> := [];
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant num == 0 ==> |digits| > 0
    {
        var digit := num % 10;
        var digitChar := intToChar(digit);
        digits := [digitChar] + digits;
        num := num / 10;
    }
    
    return digits;
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
    var n := num;
    
    var i := 9;
    while i > 1
        invariant 1 <= i <= 9
        invariant ans >= 0
        invariant mul >= 1
        invariant n >= 1
        invariant ans <= 1000000000
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant ans >= 0
            invariant mul >= 1
            invariant ans <= 1000000000
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            mul := mul * 10;
            
            // Prevent overflow
            if ans > 1000000000 || mul > 100000000 {
                return 0;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 {
        return ans;
    } else {
        return 0;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        return 1;
    }
    
    var s := intToString(n);
    var digits := s;
    
    var i := 1;
    while i < |digits| && digitToInt(digits[i-1]) <= digitToInt(digits[i])
        invariant 1 <= i <= |digits|
        invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
    {
        i := i + 1;
    }
    
    if i < |digits| {
        while i > 0 && i < |digits| && digitToInt(digits[i-1]) > digitToInt(digits[i])
            invariant 0 <= i < |digits|
            invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
        {
            var prevDigit := digitToInt(digits[i-1]);
            if prevDigit > 0 {
                digits := digits[i-1 := intToChar(prevDigit - 1)];
            }
            i := i - 1;
        }
        
        i := i + 1;
        while i < |digits|
            invariant 0 <= i <= |digits|
            invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
        {
            digits := digits[i := '9'];
            i := i + 1;
        }
    }
    
    var res := stringToInt(digits);
    if res == 0 {
        return 1;
    }
    if res > 1000000000 {
        return 1000000000;
    }
    return res;
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant a1 >= 1
        decreases cnt
    {
        if i % 2 == 1 {
            an := an - step;
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    return a1;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures true
{
    var o1 := smallestFactorization_625(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    var o3 := lastRemaining_390(o2);
    return o3;
}
