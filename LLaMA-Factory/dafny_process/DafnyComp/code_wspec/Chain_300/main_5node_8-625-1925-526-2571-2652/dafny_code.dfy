
method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 2147483647
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var n := num;
    
    var i := 9;
    while i > 1
        invariant 1 <= i <= 9
        invariant ans >= 0
        invariant mul >= 1
        invariant n >= 1
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if ans > 2147483647 || mul > 214748364 {
                return 0;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 {
        return ans;
    } else {
        return 0;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result
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
    
    if ans == 0 {
        return 1;
    } else {
        return ans;
    }
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures x < (isqrt(x) + 1) * (isqrt(x) + 1) || x >= 625
{
    if x == 0 then 0
    else if x < 4 then 1
    else if x < 9 then 2
    else if x < 16 then 3
    else if x < 25 then 4
    else if x < 36 then 5
    else if x < 49 then 6
    else if x < 64 then 7
    else if x < 81 then 8
    else if x < 100 then 9
    else if x < 121 then 10
    else if x < 144 then 11
    else if x < 169 then 12
    else if x < 196 then 13
    else if x < 225 then 14
    else if x < 256 then 15
    else if x < 289 then 16
    else if x < 324 then 17
    else if x < 361 then 18
    else if x < 400 then 19
    else if x < 441 then 20
    else if x < 484 then 21
    else if x < 529 then 22
    else if x < 576 then 23
    else if x < 625 then 24
    else 25
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 100000
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var count := dfs(1, n, vis);
    if count == 0 {
        return 1;
    } else {
        return count;
    }
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    ensures count >= 0
    ensures count <= 100000
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant count >= 0
        invariant count <= 100000
    {
        if (j % pos == 0 || pos % j == 0) && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            count := count + subCount;
            if count > 100000 {
                count := 100000;
            }
            vis[j] := false;
        }
        j := j + 1;
    }
    
    return count;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 1000
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ans >= 0
        invariant cnt >= 0
        invariant ans <= 1000
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
        if ans > 1000 {
            ans := 1000;
        }
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    if ans > 1000 {
        ans := 1000;
    }
    
    if ans == 0 {
        return 1;
    } else {
        return ans;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    return sum;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := smallestFactorization_625(o);
    if o1 == 0 || o1 > 250 {
        result := 0;
        return;
    }
    
    var o2 := countTriples_1925(o1);
    if o2 > 15 {
        result := 0;
        return;
    }
    
    var o3 := countArrangement_526(o2);
    var o4 := minOperations_2571(o3);
    var o5 := sumOfMultiples_2652(o4);
    
    result := o5;
}
