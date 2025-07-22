
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures ans >= 0
{
    ans := 0;
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
    while (result + 1) * (result + 1) <= x
        invariant result >= 0
        invariant result * result <= x
    {
        result := result + 1;
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
        invariant 0 <= k <= 3
        invariant |stk| >= 1
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
            var newVal := top / x;
            if newVal > 1000000000000000 {
                newVal := 1000000000000000;
            } else if newVal < -1000000000000000 {
                newVal := -1000000000000000;
            }
            stk := stk[..|stk| - 1] + [newVal];
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

method abs(x: int) returns (result: int)
    ensures result >= 0
    ensures result == x || result == -x
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

method smallestNumber_2165(num: int) returns (ans: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures -2147483648 <= ans <= 2147483648
{
    var neg := num < 0;
    var absNum := abs(num);
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := absNum;
    while temp > 0
        invariant temp >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
    {
        cnt[temp % 10] := cnt[temp % 10] + 1;
        temp := temp / 10;
    }
    
    ans := 0;
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant 0 <= ans <= 2147483648
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant 0 <= ans <= 2147483648
            {
                if ans > 214748364 || (ans == 214748364 && i > 8) {
                    ans := 2147483648;
                    return;
                }
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        ans := -ans;
    } else {
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
            invariant 0 <= ans <= 2147483648
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant 0 <= ans <= 2147483648
            {
                if ans > 214748364 || (ans == 214748364 && i > 7) {
                    ans := 2147483648;
                    return;
                }
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
    }
}

method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 1 <= ans <= 15
{
    ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var temp := x;
    
    while temp != 0
        invariant -2147483648 <= temp <= 2147483648
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            ans := 1;
            return;
        }
        var y := temp % 10;
        if temp < 0 && y > 0 {
            y := y - 10;
        }
        ans := ans * 10 + y;
        temp := (temp - y) / 10;
    }
    
    if ans < 1 {
        ans := 1;
    } else if ans > 15 {
        ans := 15;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 0
{
    var matchArray := new seq<int>[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        matchArray[i] := [];
        i := i + 1;
    }
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant forall k :: 1 <= k < i ==> |matchArray[k]| >= 0
    {
        var j := 1;
        while j <= n
            invariant 1 <= j <= n + 1
        {
            if j % i == 0 || i % j == 0 {
                matchArray[i] := matchArray[i] + [j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    var vis := new bool[n + 1];
    i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    result := dfs(1, n, matchArray, vis);
}

method dfs(pos: int, n: int, matchArray: array<seq<int>>, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires matchArray.Length == n + 1
    requires vis.Length == n + 1
    ensures count >= 0
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var i := 0;
    while i < |matchArray[pos]|
        invariant 0 <= i <= |matchArray[pos]|
        invariant count >= 0
    {
        var j := matchArray[pos][i];
        if 1 <= j <= n && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, matchArray, vis);
            count := count + subCount;
            vis[j] := false;
        }
        i := i + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures 0 <= result
{
    var o1 := countTriples_1925(o);
    
    var o2: int;
    if o1 >= 1 && o1 <= 10000 {
        o2 := clumsy_1006(o1);
    } else {
        o2 := 0;
    }
    
    var o3: int;
    if o2 >= -1000000000000000 && o2 <= 1000000000000000 {
        o3 := smallestNumber_2165(o2);
    } else {
        o3 := 1;
    }
    
    var o4 := reverse_7(o3);
    var o5 := countArrangement_526(o4);
    result := o5;
}
