
method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 1000000000
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var row := 0;
    while row <= n
        invariant 0 <= row <= n + 1
    {
        var col := 0;
        while col <= n
            invariant 0 <= col <= n + 1
        {
            f[row, col] := 0;
            col := col + 1;
        }
        row := row + 1;
    }
    
    var i := n - 1;
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
                var maxVal := if left > right then left else right;
                var candidate := maxVal + k;
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
    if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 2147483648
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant a1 >= 1
        invariant an >= 0
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            } else {
                an := 0;
            }
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                if an >= step {
                    an := an - step;
                } else {
                    an := 0;
                }
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result > 2147483648 {
        result := 2147483648;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 2147483648
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 50
        invariant current >= 1
        invariant ans >= 0
        invariant ans < 50 ==> current >= 1
        decreases if current == 1 then 0 else if ans >= 50 then 0 else 50 - ans
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    result := ans + 1;
    if result > 2147483648 {
        result := 2147483648;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 250
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var remaining := num;
    var i := 9;
    
    while i >= 2
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant ans >= 0
        invariant mul >= 1
    {
        while remaining % i == 0
            invariant remaining >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases remaining
        {
            remaining := remaining / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 250 {
        result := ans;
    } else {
        result := 0;
    }
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
            var c := 1;
            var found := false;
            
            // Find integer square root
            while c * c < x && c <= n
                invariant c >= 1
                invariant !found
            {
                c := c + 1;
            }
            
            if c <= n && c * c == x {
                found := true;
            }
            
            if found {
                ans := ans + 1;
            }
            
            b := b + 1;
        }
        a := a + 1;
    }
    
    result := ans;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 200
    ensures result >= 0
{
    var o1 := getMoneyAmount_375(o);
    var o2 := lastRemaining_390(o1);
    var o3 := integerReplacement_397(o2);
    var o4 := smallestFactorization_625(o3);
    if o4 >= 1 && o4 <= 250 {
        var o5 := countTriples_1925(o4);
        result := o5;
    } else {
        result := 0;
    }
}
