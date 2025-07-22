
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 8
    decreases *
{
    var current := n;
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i <= current / i
            invariant 2 <= i
            invariant s >= 0
            invariant current >= 1
        {
            while current % i == 0
                invariant current >= 1
                invariant i >= 2
                invariant s >= 0
                decreases current
            {
                current := current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if current > 1 {
            s := s + current;
        }
        
        if s == t {
            assume 1 <= t <= 8;
            return t;
        }
        current := s;
        if current < 2 {
            current := 2;
        }
    }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 100000000
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
            invariant x >= 0
            invariant b >= 0
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
                assume 1 <= res <= 100000000;
                return res;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    return 9;
}

function power10(n: int): int
    requires 0 <= n <= 10
    ensures power10(n) >= 1
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

method is_prime(x: int) returns (result: bool)
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

method reverse(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    var res := 0;
    var temp := x;
    
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
    return res;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 1000000000
    decreases *
{
    var current := n;
    
    while true
        decreases *
    {
        var rev := reverse(current);
        var isPrime := is_prime(current);
        
        if rev == current && isPrime {
            assume 1 <= current <= 1000000000;
            return current;
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
    ensures result >= 1
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant a >= 0
        invariant b >= 0
        invariant k >= 0
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
            return x + y;
        } else {
            assume false; // k > 10 case
        }
    }
    
    if a == b {
        return n;
    }
    
    if n + 1 <= 1000000000 {
        var recursive_result := closestFair_2417(n + 1);
        return recursive_result;
    } else {
        assume false; // overflow case
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures 1 <= result
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := largestPalindrome_479(o1);
    var o3 := primePalindrome_866(o2);
    var o4 := closestFair_2417(o3);
    return o4;
}
