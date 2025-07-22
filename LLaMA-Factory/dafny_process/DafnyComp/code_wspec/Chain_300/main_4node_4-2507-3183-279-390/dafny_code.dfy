
method smallestValue_2507(n0: int) returns (result: int)
    requires 2 <= n0 <= 100000
    ensures 1 <= result <= 100000
    decreases *
{
    var n := n0;
    while true
        invariant 2 <= n
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
                invariant n >= 1
                invariant i >= 2
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
            if t <= 100000 {
                return t;
            } else {
                return 100000;
            }
        }
        if s >= 2 {
            n := s;
        } else {
            return 2;
        }
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 10000
{
    var mod := 1000000007;
    var coins := [1, 2, 6];
    var f := new int[n + 1];
    
    // Initialize array
    var k := 0;
    while k <= n
        invariant 0 <= k <= n + 1
    {
        f[k] := 0;
        k := k + 1;
    }
    f[0] := 1;
    
    // Process each coin
    var coinIdx := 0;
    while coinIdx < 3
        invariant 0 <= coinIdx <= 3
        invariant f[0] == 1
    {
        var x := coins[coinIdx];
        var j := x;
        while j <= n
            invariant x <= j
            invariant f[0] == 1
        {
            f[j] := (f[j] + f[j - x]) % mod;
            j := j + 1;
        }
        coinIdx := coinIdx + 1;
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    // Ensure result is in valid range
    if ans == 0 {
        return 1;
    }
    return (ans % 10000) + 1;
}

function sqrt_approx(n: int): int
    requires n >= 0
    ensures sqrt_approx(n) >= 0
    ensures sqrt_approx(n) * sqrt_approx(n) <= n
    ensures n < 10000 ==> (sqrt_approx(n) + 1) * (sqrt_approx(n) + 1) > n
{
    if n == 0 then 0
    else if n <= 3 then 1
    else if n <= 8 then 2
    else if n <= 15 then 3
    else if n <= 24 then 4
    else if n <= 35 then 5
    else if n <= 48 then 6
    else if n <= 63 then 7
    else if n <= 80 then 8
    else if n <= 99 then 9
    else if n <= 120 then 10
    else if n <= 143 then 11
    else if n <= 168 then 12
    else if n <= 195 then 13
    else if n <= 224 then 14
    else if n <= 255 then 15
    else if n <= 288 then 16
    else if n <= 323 then 17
    else if n <= 360 then 18
    else if n <= 399 then 19
    else if n <= 440 then 20
    else if n <= 483 then 21
    else if n <= 528 then 22
    else if n <= 575 then 23
    else if n <= 624 then 24
    else if n <= 675 then 25
    else if n <= 728 then 26
    else if n <= 783 then 27
    else if n <= 840 then 28
    else if n <= 899 then 29
    else if n <= 960 then 30
    else if n <= 1023 then 31
    else if n <= 1088 then 32
    else if n <= 1155 then 33
    else if n <= 1224 then 34
    else if n <= 1295 then 35
    else if n <= 1368 then 36
    else if n <= 1443 then 37
    else if n <= 1520 then 38
    else if n <= 1599 then 39
    else if n <= 1680 then 40
    else if n <= 1763 then 41
    else if n <= 1848 then 42
    else if n <= 1935 then 43
    else if n <= 2024 then 44
    else if n <= 2115 then 45
    else if n <= 2208 then 46
    else if n <= 2303 then 47
    else if n <= 2400 then 48
    else if n <= 2499 then 49
    else if n <= 2600 then 50
    else if n <= 2703 then 51
    else if n <= 2808 then 52
    else if n <= 2915 then 53
    else if n <= 3024 then 54
    else if n <= 3135 then 55
    else if n <= 3248 then 56
    else if n <= 3363 then 57
    else if n <= 3480 then 58
    else if n <= 3599 then 59
    else if n <= 3720 then 60
    else if n <= 3843 then 61
    else if n <= 3968 then 62
    else if n <= 4095 then 63
    else if n <= 4224 then 64
    else if n <= 4355 then 65
    else if n <= 4488 then 66
    else if n <= 4623 then 67
    else if n <= 4760 then 68
    else if n <= 4899 then 69
    else if n <= 5040 then 70
    else if n <= 5183 then 71
    else if n <= 5328 then 72
    else if n <= 5475 then 73
    else if n <= 5624 then 74
    else if n <= 5775 then 75
    else if n <= 5928 then 76
    else if n <= 6083 then 77
    else if n <= 6240 then 78
    else if n <= 6399 then 79
    else if n <= 6560 then 80
    else if n <= 6723 then 81
    else if n <= 6888 then 82
    else if n <= 7055 then 83
    else if n <= 7224 then 84
    else if n <= 7395 then 85
    else if n <= 7568 then 86
    else if n <= 7743 then 87
    else if n <= 7920 then 88
    else if n <= 8099 then 89
    else if n <= 8280 then 90
    else if n <= 8463 then 91
    else if n <= 8648 then 92
    else if n <= 8835 then 93
    else if n <= 9024 then 94
    else if n <= 9215 then 95
    else if n <= 9408 then 96
    else if n <= 9603 then 97
    else if n <= 9800 then 98
    else if n <= 9999 then 99
    else 100
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000000000
{
    var m := sqrt_approx(n);
    var inf := 1000000001;
    
    // Create 2D array f[m+1][n+1]
    var f := new int[m + 1, n + 1];
    
    // Initialize array
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := inf;
            j := j + 1;
        }
        i := i + 1;
    }
    f[0, 0] := 0;
    
    // Fill DP table
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
    
    var res := f[m, n];
    if res >= inf {
        return 1;
    }
    if res < 1 {
        return 1;
    }
    return res;
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant 1 <= a1
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

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures 1 <= result
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := numberOfWays_3183(o1);
    var o3 := numSquares_279(o2);
    var o4 := lastRemaining_390(o3);
    return o4;
}
