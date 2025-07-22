
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 100000
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
            invariant t <= mx
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 {
                    return 1337;
                } else {
                    return res;
                }
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 0 <= result
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases num
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    return ans;
}

method smallestNumber_2165(num: int) returns (result: int)
    requires 0 <= num
    ensures 1 <= result <= 250
{
    var n := num;
    var cnt := new int[10];
    var i := 0;
    
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
        invariant forall k :: 0 <= k < i ==> cnt[k] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    if n == 0 {
        return 1;
    }
    
    while n > 0
        invariant n >= 0
        invariant cnt.Length == 10
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        decreases n
    {
        cnt[n % 10] := cnt[n % 10] + 1;
        n := n / 10;
    }
    
    var ans := 0;
    
    if cnt[0] > 0 {
        i := 1;
        while i < 10
            invariant 1 <= i <= 10
            invariant cnt.Length == 10
        {
            if cnt[i] > 0 {
                ans := i;
                cnt[i] := cnt[i] - 1;
                break;
            }
            i := i + 1;
        }
    }
    
    i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
        invariant ans >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
    {
        var j := 0;
        while j < cnt[i]
            invariant 0 <= j <= cnt[i]
            invariant cnt.Length == 10
            invariant ans >= 0
            invariant cnt[i] >= 0
            decreases cnt[i] - j
        {
            ans := ans * 10 + i;
            j := j + 1;
        }
        i := i + 1;
    }
    
    if ans == 0 {
        return 1;
    } else if ans > 250 {
        return 250;
    } else {
        return ans;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
{
    var ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
        decreases n - a
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
            decreases n - b
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    return ans;
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

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x
    ensures x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    var r := x;
    while r * r > x
        invariant r > 0
        decreases r
    {
        r := (r + x / r) / 2;
    }
    
    while (r + 1) * (r + 1) <= x
        invariant r >= 0
        invariant r * r <= x
        decreases x - r * r
    {
        r := r + 1;
    }
    
    return r;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := minOperations_2571(o1);
    var o3 := smallestNumber_2165(o2);
    var o4 := countTriples_1925(o3);
    return o4;
}
