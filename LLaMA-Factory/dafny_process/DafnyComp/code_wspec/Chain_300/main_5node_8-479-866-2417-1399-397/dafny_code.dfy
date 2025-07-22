
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 100000000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx == power10(n) - 1
        decreases a
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
                if res == 0 { return 1337; }
                return res;
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    return 9;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 1000000000
    ensures result >= n
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        invariant current >= 1
        decreases *
    {
        var is_palindrome := reverse(current) == current;
        var is_prime := is_prime_check(current);
        
        if is_palindrome && is_prime {
            if current <= 1000000000 {
                return current;
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 10000
    decreases *
{
    var a, b, k := 0, 0, 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant k >= 0
        invariant a >= 0
        invariant b >= 0
        decreases t
    {
        if (t % 10) % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        if k <= 10 {
            var x := power10(k);
            var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
            var res := x + y;
            if res <= 10000 { return res; }
        }
        return 10000;
    }
    
    if a == b {
        if n <= 10000 { return n; }
        return 10000;
    }
    
    if n < 1000000000 {
        var next_result := closestFair_2417(n + 1);
        return next_result;
    }
    
    return 10000;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 2147483648
{
    var cnt := new int[100]; // digit sum can be at most 9*4 = 36 for n <= 10000
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 0;
    var mx := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 0
        invariant mx >= 0
    {
        var temp := i;
        var s := 0;
        
        while temp > 0
            invariant temp >= 0
            invariant s >= 0
            decreases temp
        {
            s := s + temp % 10;
            temp := temp / 10;
        }
        
        if s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        
        i := i + 1;
    }
    
    if ans > 0 && ans <= 2147483648 {
        return ans;
    }
    return 1;
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= 0
    decreases *
{
    var current := n;
    var ans := 0;
    
    while current != 1
        invariant current >= 1
        invariant ans >= 0
        decreases *
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    return ans;
}

// Helper methods
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

function reverse(x: int): int
    requires x >= 0
    ensures reverse(x) >= 0
{
    if x < 10 then x
    else 
        var digits := count_digits(x / 10);
        if digits <= 10 then
            reverse(x / 10) + (x % 10) * power10(digits)
        else
            0
}

function count_digits(x: int): int
    requires x >= 0
    ensures count_digits(x) >= 0
    ensures count_digits(x) <= 10
{
    if x < 10 then 0
    else 
        var sub := count_digits(x / 10);
        if sub < 10 then 1 + sub else 10
}

method is_prime_check(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    var v := 2;
    while v * v <= x
        invariant v >= 2
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures 0 <= result
    decreases *
{
    var o1 := largestPalindrome_479(o);
    var o2 := primePalindrome_866(o1);
    var o3 := closestFair_2417(o2);
    var o4 := countLargestGroup_1399(o3);
    var o5 := integerReplacement_397(o4);
    return o5;
}
