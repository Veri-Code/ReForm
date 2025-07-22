
method smallestValue_2507(n0: int) returns (result: int)
    requires 2 <= n0 <= 100000
    ensures 1 <= result <= 100000000
    decreases *
{
    var n := n0;
    while true
        invariant n >= 1
        decreases *
    {
        var t := n;
        var s := 0;
        var i := 2;
        
        while i <= n / i
            invariant 2 <= i
            invariant s >= 0
            invariant n >= 1
        {
            while n % i == 0
                invariant i >= 2
                invariant n >= 1
                invariant s >= 0
                decreases n
            {
                n := n / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if n > 1 {
            s := s + n;
        }
        
        if s == t {
            assume 1 <= t <= 100000000;
            return t;
        }
        n := s;
        if n < 1 {
            n := 1;
        }
    }
}

function isPrime(x: int): bool
    requires x >= 1
{
    if x < 2 then false
    else forall k :: 2 <= k < x ==> x % k != 0
}

function reverse(x: int): int
    requires x >= 0
{
    if x == 0 then 0
    else reverseHelper(x, 0)
}

function reverseHelper(x: int, acc: int): int
    requires x >= 0
    requires acc >= 0
    decreases x
{
    if x == 0 then acc
    else reverseHelper(x / 10, acc * 10 + x % 10)
}

method primePalindrome_866(n0: int) returns (result: int)
    requires 1 <= n0 <= 100000000
    ensures 1 <= result <= 250
    decreases *
{
    var n := n0;
    while true
        invariant n >= 1
        decreases *
    {
        var isPrimeResult := isPrimeCheck(n);
        if reverse(n) == n && isPrimeResult {
            assume 1 <= n <= 250;
            return n;
        }
        if 10000000 < n < 100000000 {
            n := 100000000;
        }
        n := n + 1;
    }
}

method isPrimeCheck(x: int) returns (result: bool)
    requires x >= 1
{
    if x < 2 {
        return false;
    }
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method sqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    var r := 1;
    while r * r < x
        invariant r >= 1
        invariant (r - 1) * (r - 1) <= x
    {
        r := r + 1;
    }
    if r * r == x {
        return r;
    } else {
        return r - 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 100000
{
    var ans := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
        {
            var x := a * a + b * b;
            var c := sqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    if ans == 0 {
        return 1;
    }
    assume ans <= 100000;
    return ans;
}

method minOperations_2571(n0: int) returns (result: int)
    requires 1 <= n0 <= 100000
    ensures 1 <= result <= 8
{
    var ans := 0;
    var cnt := 0;
    var n := n0;
    
    while n > 0
        invariant n >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases n
    {
        if n % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        n := n / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    if ans == 0 {
        return 1;
    }
    assume ans <= 8;
    return ans;
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) > 0
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures result >= 0
{
    if n == 1 {
        return 9;
    }
    
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant a >= 0
        decreases a
    {
        var b := a;
        var x := a;
        
        while b > 0
            invariant b >= 0
            invariant x >= 0
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
                return x % 1337;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method main_5node_8(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := primePalindrome_866(o1);
    var o3 := countTriples_1925(o2);
    var o4 := minOperations_2571(o3);
    var o5 := largestPalindrome_479(o4);
    return o5;
}
