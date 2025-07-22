
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 0 <= result <= 1000000000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 < a <= mx || a == mx / 10
        invariant mx == power10(n) - 1
        decreases a - mx / 10
    {
        var b := a;
        var x := a;
        
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            invariant t <= mx
            decreases t
        {
            if x % t == 0 {
                result := x % 1337;
                return;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    result := 9;
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        result := 1;
        return;
    }
    
    var s := intToDigits(n);
    var i := 1;
    
    while i < |s| && charToInt(s[i-1]) <= charToInt(s[i])
        invariant 1 <= i <= |s|
        invariant |s| >= 1
        decreases |s| - i
    {
        i := i + 1;
    }
    
    if i < |s| {
        while i > 0 && charToInt(s[i-1]) > charToInt(s[i])
            invariant 0 <= i < |s|
            invariant |s| >= 1
            decreases i
        {
            s := s[i-1 := intToChar(charToInt(s[i-1]) - 1)];
            i := i - 1;
        }
        i := i + 1;
        while i < |s|
            invariant i <= |s|
            decreases |s| - i
        {
            s := s[i := '9'];
            i := i + 1;
        }
    }
    
    result := digitsToInt(s);
    if result == 0 { result := 1; }
    if result > 1000000000 { result := 1000000000; }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 500000
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    if result == 0 { result := 1; }
    if result > 500000 { result := 500000; }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant x >= 0
        invariant |stk| >= 1
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            var top := stk[|stk|-1];
            stk := stk[..|stk|-1] + [top * x];
        } else if k == 1 {
            var top := stk[|stk|-1];
            stk := stk[..|stk|-1] + [top / x];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := sumArray(stk);
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures true
{
    var o1 := largestPalindrome_479(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    if o2 > 1000 {
        o2 := 1000;
    }
    var o3 := sumOfMultiples_2652(o2);
    if o3 > 10000 {
        o3 := 10000;
    }
    result := clumsy_1006(o3);
}

// Helper functions
function power10(n: int): int
    requires 0 <= n <= 10
    ensures power10(n) > 0
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else if n == 8 then 100000000
    else if n == 9 then 1000000000
    else 10000000000
}

method intToDigits(n: int) returns (digits: string)
    requires n >= 0
    ensures |digits| >= 1
{
    if n == 0 {
        digits := "0";
    } else {
        digits := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant temp == 0 ==> |digits| >= 1
            decreases temp
        {
            var digit := temp % 10;
            digits := [intToChar(digit)] + digits;
            temp := temp / 10;
        }
    }
}

function intToChar(n: int): char
    requires 0 <= n <= 9
{
    if n == 0 then '0'
    else if n == 1 then '1'
    else if n == 2 then '2'
    else if n == 3 then '3'
    else if n == 4 then '4'
    else if n == 5 then '5'
    else if n == 6 then '6'
    else if n == 7 then '7'
    else if n == 8 then '8'
    else '9'
}

function charToInt(c: char): int
    ensures 0 <= charToInt(c) <= 9
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else 9
}

method digitsToInt(digits: string) returns (result: int)
    requires |digits| >= 1
    ensures result >= 0
{
    result := 0;
    var i := 0;
    
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
        decreases |digits| - i
    {
        result := result * 10 + charToInt(digits[i]);
        i := i + 1;
    }
}

method sumArray(arr: seq<int>) returns (sum: int)
{
    sum := 0;
    var i := 0;
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        decreases |arr| - i
    {
        sum := sum + arr[i];
        i := i + 1;
    }
}
