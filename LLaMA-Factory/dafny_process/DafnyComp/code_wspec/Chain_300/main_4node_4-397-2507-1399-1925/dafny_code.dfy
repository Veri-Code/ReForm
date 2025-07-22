
method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 2 <= result <= 100000
    decreases *
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 100000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 100000
        decreases *
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && (current % 4 == 3) {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    result := if ans >= 2 then ans else 2;
}

method sumOfPrimeFactors(n: int) returns (sum: int)
    requires n >= 2
    ensures sum >= 2
{
    var current := n;
    var s := 0;
    var i := 2;
    
    while i * i <= current
        invariant i >= 2
        invariant current >= 1
        invariant s >= 0
        decreases current - i + 1
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
    
    sum := if s >= 2 then s else 2;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 10000
    decreases *
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 1
        invariant iterations >= 0
    {
        var t := current;
        var s := sumOfPrimeFactors(current);
        
        if s == t {
            result := if t <= 10000 then t else 10000;
            return;
        }
        current := s;
        iterations := iterations + 1;
    }
    
    result := if current <= 10000 then current else 1;
}

method digitSum(n: int) returns (sum: int)
    requires n >= 1
    ensures sum >= 1
{
    var current := n;
    var s := 0;
    
    while current > 0
        invariant current >= 0
        invariant s >= 0
        decreases current
    {
        s := s + (current % 10);
        current := current / 10;
    }
    
    sum := if s >= 1 then s else 1;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 250
{
    var cnt := new int[46];
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 1;
    var mx := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 1
        invariant mx >= 0
        invariant ans <= 250
    {
        var s := digitSum(i);
        if s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := if ans < 250 then ans + 1 else 250;
            }
        }
        i := i + 1;
    }
    
    result := ans;
}

method isqrt(x: int) returns (root: int)
    requires x >= 0
    ensures root >= 0
    ensures root * root <= x
    ensures (root + 1) * (root + 1) > x
{
    if x == 0 {
        return 0;
    }
    
    var r := x;
    while r * r > x
        invariant r >= 0
        decreases r
    {
        r := (r + x / r) / 2;
    }
    
    while (r + 1) * (r + 1) <= x
        invariant r >= 0
        invariant r * r <= x
    {
        r := r + 1;
    }
    
    root := r;
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
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
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
    
    result := ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
    decreases *
{
    var o1 := integerReplacement_397(o);
    var o2 := smallestValue_2507(o1);
    var o3 := countLargestGroup_1399(o2);
    var o4 := countTriples_1925(o3);
    result := o4;
}
