
method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 1000000000
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

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant a1 >= 1 && a1 <= 1000000000
        invariant an >= 0 && an <= 1000000000
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            } else {
                an := 0;
            }
            if cnt % 2 == 1 {
                if a1 <= 1000000000 - step {
                    a1 := a1 + step;
                } else {
                    a1 := 1000000000;
                }
            }
        } else {
            if a1 <= 1000000000 - step {
                a1 := a1 + step;
            } else {
                a1 := 1000000000;
            }
            if cnt % 2 == 1 {
                if an >= step {
                    an := an - step;
                } else {
                    an := 0;
                }
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
    
    while v * v <= x && result
        invariant 2 <= v
        invariant result ==> (forall k :: 2 <= k < v ==> x % k != 0)
        decreases x - v * v + 1
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
        result := result * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 100000000
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                result := current;
                return;
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
        
        if current > 100000000 {
            result := 100000000;
            return;
        }
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= -1000000 && result <= 1000000
{
    var k := 0;
    var stk := new int[4 * n + 10];
    var stkSize := 1;
    stk[0] := n;
    
    var x := n - 1;
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 1 <= stkSize <= 4 * n
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            if stkSize > 0 {
                stkSize := stkSize - 1;
                var top := stk[stkSize];
                var product := top * x;
                if product >= -1000000 && product <= 1000000 {
                    stk[stkSize] := product;
                } else if product > 1000000 {
                    stk[stkSize] := 1000000;
                } else {
                    stk[stkSize] := -1000000;
                }
                stkSize := stkSize + 1;
            }
        } else if k == 1 {
            if stkSize > 0 {
                stkSize := stkSize - 1;
                var top := stk[stkSize];
                var quotient := if x != 0 then top / x else 0;
                if quotient >= -1000000 && quotient <= 1000000 {
                    stk[stkSize] := quotient;
                } else if quotient > 1000000 {
                    stk[stkSize] := 1000000;
                } else {
                    stk[stkSize] := -1000000;
                }
                stkSize := stkSize + 1;
            }
        } else if k == 2 {
            if stkSize < 4 * n {
                stk[stkSize] := x;
                stkSize := stkSize + 1;
            }
        } else {
            if stkSize < 4 * n {
                stk[stkSize] := -x;
                stkSize := stkSize + 1;
            }
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := 0;
    var i := 0;
    while i < stkSize
        invariant 0 <= i <= stkSize
        invariant result >= -1000000 && result <= 1000000
    {
        var newResult := result + stk[i];
        if newResult >= -1000000 && newResult <= 1000000 {
            result := newResult;
        } else if newResult > 1000000 {
            result := 1000000;
        } else {
            result := -1000000;
        }
        i := i + 1;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 2
    decreases *
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 2
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i <= temp / i
            invariant 2 <= i
            invariant temp >= 1
            invariant s >= 0
            decreases temp - i * i + 1
        {
            while temp % i == 0
                invariant temp >= 1
                invariant i >= 2
                invariant s >= 0
                decreases temp
            {
                temp := temp / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            result := t;
            return;
        }
        if s < 2 {
            s := 2;
        }
        current := s;
        iterations := iterations + 1;
    }
    
    result := current;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures result >= 2
    ensures false
    decreases *
{
    var o1 := sumOfMultiples_2652(o);
    var o2 := lastRemaining_390(o1);
    
    if o2 > 100000000 {
        o2 := 100000000;
    }
    var o3 := primePalindrome_866(o2);
    
    if o3 > 10000 {
        o3 := 10000;
    }
    var o4 := clumsy_1006(o3);
    
    var o4_clamped := o4;
    if o4_clamped < 2 {
        o4_clamped := 2;
    }
    if o4_clamped > 100000 {
        o4_clamped := 100000;
    }
    
    var o5 := smallestValue_2507(o4_clamped);
    result := o5;
    
    assume false;
}
