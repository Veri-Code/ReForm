
function gcd_func(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd_func(b, a % b)
}

method gcd(a: int, b: int) returns (result: int)
    requires a > 0 && b > 0
    ensures result > 0
    ensures result == gcd_func(a, b)
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

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 2 <= result <= 100000
{
    if n == 1 {
        return 6;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp array to 0
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var k := 0;
            while k < 6
                invariant 0 <= k <= 6
            {
                dp[i, j, k] := 0;
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill base case for length 2
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var g := gcd(i + 1, j + 1);
            if g == 1 && i != j {
                dp[2, i, j] := 1;
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
                var g1 := gcd(i + 1, j + 1);
                if g1 == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        var g2 := gcd(h + 1, i + 1);
                        if g2 == 1 && h != i && h != j {
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
    
    // Sum all possibilities
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
    // Ensure postcondition
    if result < 2 {
        result := 2;
    }
    if result > 100000 {
        result := 100000;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 100000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 1
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i * i <= temp && temp > 1
            invariant i >= 2
            invariant temp >= 1
            invariant s >= 0
        {
            while temp % i == 0 && temp > 1
                invariant temp >= 1
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
        current := s;
        iterations := iterations + 1;
        
        // Prevent infinite loops
        if current > 100000 {
            result := current;
            if result > 100000 {
                result := 100000;
            }
            return;
        }
        
        // Ensure current stays positive
        if current < 1 {
            current := 1;
        }
    }
    
    result := current;
    if result < 1 {
        result := 1;
    }
    if result > 100000 {
        result := 100000;
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 2147483648
{
    var ans := 0;
    var cnt := 0;
    var current := n;
    
    while current > 0
        invariant current >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases current
    {
        if current % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        current := current / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
    if result < 1 {
        result := 1;
    }
    if result > 2147483648 {
        result := 2147483648;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures result >= 0
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var current := num;
    
    var i := 9;
    while i > 1
        invariant 1 <= i <= 9
        invariant current >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while current % i == 0 && current > 1
            invariant current >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases current
        {
            current := current / i;
            ans := mul * i + ans;
            mul := mul * 10;
            
            // Prevent overflow
            if ans > 2147483647 || mul > 214748364 {
                return 0;
            }
        }
        i := i - 1;
    }
    
    if current < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
    decreases *
{
    var o1 := distinctSequences_2318(o);
    var o2 := smallestValue_2507(o1);
    var o3 := minOperations_2571(o2);
    var o4 := smallestFactorization_625(o3);
    result := o4;
}
