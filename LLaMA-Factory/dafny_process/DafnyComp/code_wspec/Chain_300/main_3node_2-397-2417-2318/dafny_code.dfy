
method gcd(a: int, b: int) returns (result: int)
    requires a > 0 && b > 0
    ensures result > 0
    ensures result <= a && result <= b
{
    var x := a;
    var y := b;
    while y != 0
        invariant x > 0 && y >= 0
        invariant gcd_func(a, b) == gcd_func(x, y)
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    result := x;
}

function gcd_func(a: int, b: int): int
    requires a > 0 && b >= 0
    ensures gcd_func(a, b) > 0
    ensures gcd_func(a, b) <= a
    ensures b > 0 ==> gcd_func(a, b) <= b
    decreases if b == 0 then 0 else b
{
    if b == 0 then a
    else gcd_func(b, a % b)
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= 0
    ensures result <= 1000000000
    ensures 1 <= result <= 1000000000
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 1000000000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 1000000000
        decreases if current == 1 then 0 else 1000000000 - ans
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
    
    if ans == 0 {
        result := 1;
    } else {
        result := ans;
    }
}

method countDigits(n: int) returns (evenCount: int, oddCount: int, totalDigits: int)
    requires n >= 1
    ensures evenCount >= 0 && oddCount >= 0 && totalDigits >= 1
    ensures evenCount + oddCount == totalDigits
{
    var t := n;
    var a := 0;  // odd count
    var b := 0;  // even count
    var k := 0;  // total digits
    
    while t > 0
        invariant t >= 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        invariant if t == 0 then k >= 1 else true
        decreases t
    {
        var digit := t % 10;
        if digit % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    evenCount := b;
    oddCount := a;
    totalDigits := k;
}

method power10(exp: int) returns (result: int)
    requires exp >= 0 && exp <= 10
    ensures result >= 1
{
    result := 1;
    var i := 0;
    while i < exp
        invariant 0 <= i <= exp
        invariant result >= 1
        decreases exp - i
    {
        result := result * 10;
        i := i + 1;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 1
    ensures result <= 10000
    decreases if n <= 10000 then 10000 - n else 0
{
    if n > 10000 {
        result := 10000;
        return;
    }
    
    var evenCount, oddCount, totalDigits := countDigits(n);
    
    if totalDigits % 2 == 1 {
        // Odd number of digits, need to go to next even-digit number
        if totalDigits <= 10 {
            var x := power10(totalDigits);
            var halfDigits := totalDigits / 2;
            var y := 0;
            if halfDigits > 0 {
                var i := 0;
                y := 1;
                while i < halfDigits - 1
                    invariant 0 <= i <= halfDigits - 1
                    invariant y >= 1
                    decreases halfDigits - 1 - i
                {
                    y := y * 10 + 1;
                    i := i + 1;
                }
            }
            if x + y <= 10000 {
                result := x + y;
            } else {
                result := 10000;
            }
        } else {
            result := 10000;
        }
    } else if evenCount == oddCount {
        result := n;
    } else {
        if n + 1 <= 10000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 10000;
        }
    }
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 0
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    
    // Initialize dp array
    var dp := new int[n + 1, 6, 6];
    
    // Initialize for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var gcd_val := gcd_func(i + 1, j + 1);
            if gcd_val == 1 && i != j {
                dp[2, i, j] := 1;
            } else {
                dp[2, i, j] := 0;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp for lengths 3 to n
    var k := 3;
    while k <= n
        invariant 3 <= k <= n + 1
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                dp[k, i, j] := 0;
                var gcd_ij := gcd_func(i + 1, j + 1);
                if gcd_ij == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                        invariant dp[k, i, j] >= 0
                    {
                        var gcd_hi := gcd_func(h + 1, i + 1);
                        if gcd_hi == 1 && h != i && h != j {
                            dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
                        }
                        h := h + 1;
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
    
    // Sum all possibilities for length n
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant ans >= 0
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant ans >= 0
        {
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := ans;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := integerReplacement_397(o);
    var o2 := closestFair_2417(o1);
    if o2 <= 10000 {
        var o3 := distinctSequences_2318(o2);
        result := o3;
    } else {
        result := 0;
    }
}
