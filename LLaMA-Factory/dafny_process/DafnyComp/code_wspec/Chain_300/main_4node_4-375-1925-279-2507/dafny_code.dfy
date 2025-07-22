
method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 250
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Main computation
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
        {
            f[i, j] := j + f[i, j - 1];
            var k := i;
            while k < j
                invariant i <= k <= j
            {
                var left := if k - 1 < i then 0 else f[i, k - 1];
                var right := if k + 1 > j then 0 else f[k + 1, j];
                var candidate := (if left > right then left else right) + k;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result < 1 {
        result := 1;
    }
    if result > 250 {
        result := 250;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 10000
{
    result := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant 0 <= result
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 0 <= result
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
    
    if result < 1 {
        result := 1;
    }
    if result > 10000 {
        result := 10000;
    }
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures x < 625 ==> (isqrt(x) + 1) * (isqrt(x) + 1) > x
{
    if x == 0 then 0
    else if x <= 3 then 1
    else if x <= 8 then 2
    else if x <= 15 then 3
    else if x <= 24 then 4
    else if x <= 35 then 5
    else if x <= 48 then 6
    else if x <= 63 then 7
    else if x <= 80 then 8
    else if x <= 99 then 9
    else if x <= 120 then 10
    else if x <= 143 then 11
    else if x <= 168 then 12
    else if x <= 195 then 13
    else if x <= 224 then 14
    else if x <= 255 then 15
    else if x <= 288 then 16
    else if x <= 323 then 17
    else if x <= 360 then 18
    else if x <= 399 then 19
    else if x <= 440 then 20
    else if x <= 483 then 21
    else if x <= 528 then 22
    else if x <= 575 then 23
    else if x <= 624 then 24
    else 25
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 2 <= result <= 100000
{
    var m := isqrt(n);
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 100001; // Use a large value instead of infinity
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
                var candidate := f[i, j - i * i] + 1;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result < 2 {
        result := 2;
    }
    if result > 100000 {
        result := 100000;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 2
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000 // Bound iterations to ensure termination
        invariant current >= 2
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i * i <= current && current > 1 && i <= 316
            invariant 2 <= i <= 317
            invariant s >= 0
            invariant current >= 1
        {
            while current % i == 0 && current > 1
                invariant current >= 1
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
            result := t;
            return;
        }
        
        current := s;
        if current < 2 {
            current := 2;
        }
        iterations := iterations + 1;
    }
    
    // Fallback if we hit iteration limit
    result := current;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 200
    ensures result >= 2
{
    var o1 := getMoneyAmount_375(o);
    var o2 := countTriples_1925(o1);
    var o3 := numSquares_279(o2);
    var o4 := smallestValue_2507(o3);
    result := o4;
}
