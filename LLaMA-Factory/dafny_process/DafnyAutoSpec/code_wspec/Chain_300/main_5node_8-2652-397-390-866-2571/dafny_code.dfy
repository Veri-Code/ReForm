
method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 2147483648
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        invariant result <= x * 1000
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    if result == 0 {
        result := 1;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 1000000000
{
    result := 0;
    var current := n;
    
    while current != 1 && result < 50
        invariant current >= 1
        invariant result >= 0
        invariant result <= 50
        decreases 50 - result
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            if current < 2147483647 {
                current := current + 1;
            } else {
                current := current - 1;
            }
        } else {
            current := current - 1;
        }
        result := result + 1;
    }
    
    if result == 0 {
        result := 1;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1 && step <= 1000000000
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant a1 >= 1
        invariant a1 <= 100000000
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 && a1 + step <= 100000000 {
                a1 := a1 + step;
            }
        } else {
            if a1 + step <= 100000000 {
                a1 := a1 + step;
            }
            if cnt % 2 == 1 && an >= step {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        if step <= 500000000 {
            step := step * 2;
        }
        i := i + 1;
    }
    
    result := a1;
}

method isPrime(x: int) returns (result: bool)
    requires x >= 1
{
    if x < 2 {
        result := false;
        return;
    }
    
    var v := 2;
    result := true;
    
    while v * v <= x && result && v <= 1000
        invariant v >= 2
        invariant result ==> (forall k :: 2 <= k < v ==> x % k != 0)
        decreases 1000 - v + 1
    {
        if x % v == 0 {
            result := false;
        }
        v := v + 1;
    }
}

method reverse(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    result := 0;
    var temp := x;
    
    while temp > 0
        invariant temp >= 0
        invariant result >= 0
        decreases temp
    {
        if result <= 214748364 {
            result := result * 10 + temp % 10;
        }
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 100000
{
    var current := n;
    
    if current > 100000 {
        result := 100000;
        return;
    }
    
    while current <= 100000
        invariant current >= n
        invariant current >= 1
        decreases 100000 - current + 1
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                result := current;
                return;
            }
        }
        
        current := current + 1;
    }
    
    result := 100000;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
{
    result := 0;
    var cnt := 0;
    var current := n;
    
    while current > 0
        invariant current >= 0
        invariant result >= 0
        invariant cnt >= 0
        decreases current
    {
        if current % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            result := result + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        current := current / 2;
    }
    
    if cnt == 1 {
        result := result + 1;
    } else if cnt > 1 {
        result := result + 2;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures result >= 0
{
    var o1 := sumOfMultiples_2652(o);
    var o2 := integerReplacement_397(o1);
    var o3 := lastRemaining_390(o2);
    var o4 := primePalindrome_866(o3);
    var o5 := minOperations_2571(o4);
    result := o5;
}
