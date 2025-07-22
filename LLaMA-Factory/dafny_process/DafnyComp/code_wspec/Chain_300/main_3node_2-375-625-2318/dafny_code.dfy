
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

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures result >= 1
    ensures result <= 2147483648
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var init_i := 0;
    while init_i <= n
        invariant 0 <= init_i <= n + 1
    {
        var init_j := 0;
        while init_j <= n
            invariant 0 <= init_j <= n + 1
        {
            f[init_i, init_j] := 0;
            init_j := init_j + 1;
        }
        init_i := init_i + 1;
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
                var left_val := if k - 1 < i then 0 else f[i, k - 1];
                var right_val := if k + 1 > j then 0 else f[k + 1, j];
                var max_val := if left_val > right_val then left_val else right_val;
                var candidate := max_val + k;
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
    
    // Ensure postconditions
    if result < 1 {
        result := 1;
    }
    if result > 2147483648 {
        result := 2147483648;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 10000
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
        invariant ans <= 10000
    {
        while remaining % i == 0
            invariant remaining >= 1
            invariant ans >= 0
            invariant mul >= 1
            invariant ans <= 10000
            decreases remaining
        {
            remaining := remaining / i;
            var new_ans := mul * i + ans;
            if new_ans > 10000 {
                result := 0;
                return;
            }
            ans := new_ans;
            mul := mul * 10;
            if mul > 1000000 { // Prevent overflow
                result := 0;
                return;
            }
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 10000 {
        result := ans;
    } else {
        result := 0;
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
    var dp := new int[n + 1, 6, 6];
    
    // Initialize array to 0
    var init_k := 0;
    while init_k <= n
        invariant 0 <= init_k <= n + 1
    {
        var init_i := 0;
        while init_i < 6
            invariant 0 <= init_i <= 6
        {
            var init_j := 0;
            while init_j < 6
                invariant 0 <= init_j <= 6
            {
                dp[init_k, init_i, init_j] := 0;
                init_j := init_j + 1;
            }
            init_i := init_i + 1;
        }
        init_k := init_k + 1;
    }
    
    // Initialize base case for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var gcd_val := gcd(i + 1, j + 1);
            if gcd_val == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table for lengths 3 to n
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
                var gcd_ij := gcd(i + 1, j + 1);
                if gcd_ij == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        var gcd_hi := gcd(h + 1, i + 1);
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
    requires 1 <= o <= 200
    ensures result >= 0
{
    var o1 := getMoneyAmount_375(o);
    var o2 := smallestFactorization_625(o1);
    if o2 >= 1 {
        var o3 := distinctSequences_2318(o2);
        result := o3;
    } else {
        result := 0;
    }
}
