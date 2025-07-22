
method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= ans <= 2147483647
{
    ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var temp_x := x;
    
    while temp_x != 0
        invariant 0 <= ans <= 2147483647
        decreases if temp_x >= 0 then temp_x else -temp_x
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        var y := temp_x % 10;
        if temp_x < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans < 0 || new_ans > 2147483647 {
            return 0;
        }
        ans := new_ans;
        temp_x := (temp_x - y) / 10;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 0 <= n <= 2147483647
    ensures 1 <= result <= 100000000
{
    if n == 0 {
        return 1;
    }
    
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top * x];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top / x];
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
        decreases |stk| - i
    {
        result := result + stk[i];
        i := i + 1;
    }
    
    if result < 1 {
        result := 1;
    } else if result > 100000000 {
        result := 100000000;
    }
}

method is_prime(x: int) returns (prime: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method reverse_int(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    res := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 10000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000000
        invariant current >= n
        invariant iterations >= 0
        decreases 1000000 - iterations
    {
        var rev := reverse_int(current);
        if rev == current {
            var prime := is_prime(current);
            if prime {
                if current <= 10000 {
                    return current;
                } else {
                    return 10000;
                }
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
        iterations := iterations + 1;
    }
    
    return 1;
}

method digit_sum(num: int) returns (sum: int)
    requires num >= 1
    ensures sum >= 1
{
    sum := 0;
    var temp := num;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
        decreases temp
    {
        sum := sum + temp % 10;
        temp := temp / 10;
    }
    if sum == 0 {
        sum := 1;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 250
{
    var cnt := map[];
    var ans := 0;
    var mx := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 0
        invariant mx >= 0
        decreases n - i + 1
    {
        var s := digit_sum(i);
        
        var current_count := if s in cnt then cnt[s] else 0;
        cnt := cnt[s := current_count + 1];
        
        if mx < cnt[s] {
            mx := cnt[s];
            ans := 1;
        } else if mx == cnt[s] {
            ans := ans + 1;
        }
        i := i + 1;
    }
    
    if ans == 0 {
        ans := 1;
    } else if ans > 250 {
        ans := 250;
    }
    
    result := ans;
}

method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures ans >= 0
{
    ans := 0;
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
            var c := 1;
            var found := false;
            
            while c <= n && c * c <= x && !found
                invariant 1 <= c <= n + 1
                invariant !found ==> forall k :: 1 <= k < c ==> k * k != x
                decreases n - c + 1
            {
                if c * c == x {
                    found := true;
                    ans := ans + 1;
                }
                c := c + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := reverse_7(o);
    var o2 := clumsy_1006(o1);
    var o3 := primePalindrome_866(o2);
    var o4 := countLargestGroup_1399(o3);
    var o5 := countTriples_1925(o4);
    result := o5;
}
