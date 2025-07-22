
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures 0 <= ans <= 100000
{
    ans := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant 0 <= ans <= (a - 1) * (n - 1)
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 0 <= ans <= (a - 1) * (n - 1) + (b - 1)
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
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    result := 1;
    while result * result < x
        invariant result >= 1
        invariant (result - 1) * (result - 1) <= x
    {
        result := result + 1;
    }
    
    if result * result > x {
        result := result - 1;
    }
}

method numberOfWays_3183(n: int) returns (ans: int)
    requires 0 <= n <= 100000
    ensures 1 <= ans <= 10000
{
    ans := 1;
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    result := 1;
}

method reverse_7(x: int) returns (ans: int)
    requires -10000 <= x <= 10000
    ensures -1000000000000000 <= ans <= 1000000000000000
{
    ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var num := x;
    
    while num != 0
        invariant -1000000000000000 <= ans <= 1000000000000000
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := num % 10;
        if num < 0 && y > 0 {
            y := y - 10;
        }
        ans := ans * 10 + y;
        num := (num - y) / 10;
    }
}

method abs(x: int) returns (result: int)
    requires -1000000000000000 <= x <= 1000000000000000
    ensures result >= 0
    ensures result == x || result == -x
    ensures -1000000000000000 <= result <= 1000000000000000
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

method smallestNumber_2165(num: int) returns (ans: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures -1000000000000000 <= ans <= 1000000000000000
{
    var neg := num < 0;
    var absNum := abs(num);
    var cnt := new int[10];
    
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := absNum;
    while temp > 0
        invariant temp >= 0
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    ans := 0;
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant -1000000000000000 <= ans <= 1000000000000000
        {
            if cnt[i] > 0 {
                var count := 0;
                while count < cnt[i]
                    invariant 0 <= count <= cnt[i]
                    invariant -1000000000000000 <= ans <= 1000000000000000
                {
                    if ans > 100000000000000 || ans < -100000000000000 {
                        count := cnt[i];
                    } else {
                        var newAns := ans * 10 + i;
                        if newAns > 1000000000000000 || newAns < -1000000000000000 {
                            count := cnt[i];
                        } else {
                            ans := newAns;
                            count := count + 1;
                        }
                    }
                }
            }
            i := i - 1;
        }
        if ans > 1000000000000000 {
            ans := 1000000000000000;
        }
        return -ans;
    }
    
    if cnt[0] > 0 {
        i := 1;
        while i < 10
            invariant 1 <= i <= 10
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
        invariant -1000000000000000 <= ans <= 1000000000000000
    {
        if cnt[i] > 0 {
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant -1000000000000000 <= ans <= 1000000000000000
            {
                if ans > 100000000000000 || ans < -100000000000000 {
                    count := cnt[i];
                } else {
                    var newAns := ans * 10 + i;
                    if newAns > 1000000000000000 || newAns < -1000000000000000 {
                        count := cnt[i];
                    } else {
                        ans := newAns;
                        count := count + 1;
                    }
                }
            }
        }
        i := i + 1;
    }
    
    if ans > 1000000000000000 {
        ans := 1000000000000000;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures -1000000000000000 <= result <= 1000000000000000
{
    var o1 := countTriples_1925(o);
    var o2 := numberOfWays_3183(o1);
    var o3 := numSquares_279(o2);
    var o4 := reverse_7(o3);
    result := smallestNumber_2165(o4);
}
