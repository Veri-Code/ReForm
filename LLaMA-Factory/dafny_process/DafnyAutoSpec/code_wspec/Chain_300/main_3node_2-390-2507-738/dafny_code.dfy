
method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    var a1: int := 1;
    var an: int := n;
    var i: int := 0;
    var step: int := 1;
    var cnt: int := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant 1 <= a1 <= 1000000000
        invariant step <= 1000000000
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 && a1 + step <= 1000000000 {
                a1 := a1 + step;
            }
        } else {
            if a1 + step <= 1000000000 {
                a1 := a1 + step;
            }
            if cnt % 2 == 1 && an >= step {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        if step <= 500000000 {
            step := step * 2;
        }
        i := i + 1;
    }
    result := a1;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 2 <= result <= 1000000000
{
    var current: int := n;
    var iterations: int := 0;
    
    while iterations < 50
        invariant current >= 2
        invariant iterations >= 0
        invariant current <= 1000000000
        decreases 50 - iterations
    {
        var t: int := current;
        var s: int := 0;
        var i: int := 2;
        var temp: int := current;
        
        while i * i <= temp && i <= 1000
            invariant i >= 2
            invariant s >= 0
            invariant temp >= 1
            invariant current >= 1
            decreases temp - i * i + 1000
        {
            while temp % i == 0 && temp > 1
                invariant i >= 2
                invariant temp >= 1
                invariant s >= 0
                invariant current >= 1
                decreases temp
            {
                temp := temp / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            result := t;
            return;
        }
        
        if s >= 2 && s <= 1000000000 {
            current := s;
        } else {
            result := t;
            return;
        }
        iterations := iterations + 1;
    }
    
    result := current;
}

method digitToInt(c: char) returns (digit: int)
    requires '0' <= c <= '9'
    ensures 0 <= digit <= 9
{
    digit := (c as int) - ('0' as int);
}

method intToChar(d: int) returns (c: char)
    requires 0 <= d <= 9
    ensures '0' <= c <= '9'
{
    c := (d + ('0' as int)) as char;
}

method stringToInt(s: seq<char>) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
    ensures result <= 1000000000
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
        invariant result <= 1000000000
    {
        var digit := digitToInt(s[i]);
        if result <= (1000000000 - digit) / 10 {
            result := result * 10 + digit;
        }
        i := i + 1;
    }
}

method intToString(n: int) returns (s: seq<char>)
    requires n >= 0
    ensures |s| > 0
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        s := ['0'];
        return;
    }
    
    var digits: seq<char> := [];
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| > 0
        decreases temp
    {
        var digit := temp % 10;
        var c := intToChar(digit);
        digits := [c] + digits;
        temp := temp / 10;
    }
    
    s := digits;
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= 1000000000
{
    var s := intToString(n);
    var i := 1;
    
    while i < |s| && s[i-1] <= s[i]
        invariant 1 <= i <= |s|
        invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    {
        i := i + 1;
    }
    
    if i < |s| {
        while i > 0 && i < |s| && s[i-1] > s[i]
            invariant 0 <= i < |s|
            invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
        {
            var digit := digitToInt(s[i-1]);
            if digit > 0 {
                var newChar := intToChar(digit - 1);
                s := s[i-1 := newChar];
            }
            i := i - 1;
        }
        
        i := i + 1;
        while i < |s|
            invariant i <= |s|
            invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
        {
            s := s[i := '9'];
            i := i + 1;
        }
    }
    
    result := stringToInt(s);
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := lastRemaining_390(o);
    if o1 >= 2 && o1 <= 100000 {
        var o2 := smallestValue_2507(o1);
        var o3 := monotoneIncreasingDigits_738(o2);
        result := o3;
    } else {
        var o3 := monotoneIncreasingDigits_738(o1);
        result := o3;
    }
}
