
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 1000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
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
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 {
                    return 1;
                } else {
                    assert res > 0;
                    if res > 1000 {
                        return 1000;
                    } else {
                        return res;
                    }
                }
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    return 9;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 10000
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
    
    if result == 0 {
        result := 1;
    }
    
    assert result >= 1;
    if result > 10000 {
        result := 10000;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures -1000000000000000 <= result <= 1000000000000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant |stk| >= 1
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var newVal := top * x;
            if newVal > 1000000000000000 {
                newVal := 1000000000000000;
            } else if newVal < -1000000000000000 {
                newVal := -1000000000000000;
            }
            stk := stk[..|stk| - 1] + [newVal];
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
    
    result := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant -1000000000000000 <= result <= 1000000000000000
        decreases |stk| - i
    {
        var newResult := result + stk[i];
        if newResult > 1000000000000000 {
            result := 1000000000000000;
        } else if newResult < -1000000000000000 {
            result := -1000000000000000;
        } else {
            result := newResult;
        }
        i := i + 1;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
        decreases 10 - i
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        decreases temp
    {
        cnt[temp % 10] := cnt[temp % 10] + 1;
        temp := temp / 10;
    }
    
    result := 0;
    
    if neg {
        var digit := 9;
        while digit >= 0
            invariant -1 <= digit <= 9
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
            decreases digit + 1
        {
            var count := 0;
            while count < cnt[digit]
                invariant 0 <= count <= cnt[digit]
                invariant cnt[digit] >= 0
                decreases cnt[digit] - count
            {
                result := result * 10 + digit;
                count := count + 1;
            }
            digit := digit - 1;
        }
        result := -result;
    } else {
        if cnt[0] > 0 {
            var firstDigit := 1;
            while firstDigit < 10
                invariant 1 <= firstDigit <= 10
                invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
                decreases 10 - firstDigit
            {
                if cnt[firstDigit] > 0 {
                    result := firstDigit;
                    cnt[firstDigit] := cnt[firstDigit] - 1;
                    break;
                }
                firstDigit := firstDigit + 1;
            }
        }
        
        var digit := 0;
        while digit < 10
            invariant 0 <= digit <= 10
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
            decreases 10 - digit
        {
            var count := 0;
            while count < cnt[digit]
                invariant 0 <= count <= cnt[digit]
                invariant cnt[digit] >= 0
                decreases cnt[digit] - count
            {
                result := result * 10 + digit;
                count := count + 1;
            }
            digit := digit + 1;
        }
    }
}

function power10(n: int): int
    requires 0 <= n <= 8
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
    else 100000000
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures true
{
    var o1 := largestPalindrome_479(o);
    var o2 := sumOfMultiples_2652(o1);
    var o3 := clumsy_1006(o2);
    var o4 := smallestNumber_2165(o3);
    result := o4;
}
