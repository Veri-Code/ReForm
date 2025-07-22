
method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 200
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 200
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 200
        decreases if current == 1 then 0 else 200 - ans
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
    
    if current == 1 {
        result := ans;
    } else {
        result := 200;
    }
    
    if result == 0 {
        result := 1;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 250
{
    if n == 1 {
        return 1;
    }
    
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
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
                var left_cost := if k - 1 < i then 0 else f[i, k - 1];
                var right_cost := if k + 1 > j then 0 else f[k + 1, j];
                var max_cost := if left_cost > right_cost then left_cost else right_cost;
                var total_cost := max_cost + k;
                if total_cost < f[i, j] {
                    f[i, j] := total_cost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result <= 0 {
        result := 1;
    }
    if result > 250 {
        result := 250;
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
    if x == 1 {
        return 1;
    }
    
    var r := x / 2 + 1;
    while r * r > x
        invariant r >= 1
        decreases r
    {
        var new_r := (r + x / r) / 2;
        if new_r >= r {
            r := r - 1;
        } else {
            r := new_r;
        }
    }
    
    // Ensure the postcondition
    while (r + 1) * (r + 1) <= x
        invariant r >= 0
        invariant r * r <= x
        decreases x - r * r
    {
        r := r + 1;
    }
    
    result := r;
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
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    result := ans;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 0 <= result <= 2147483647
{
    if num < 2 {
        return num;
    }
    
    var current_num := num;
    var ans := 0;
    var mul := 1;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant current_num >= 1
        invariant ans >= 0
        invariant mul >= 1
    {
        while current_num % i == 0
            invariant current_num >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases current_num
        {
            current_num := current_num / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if current_num < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 0
{
    // Build match array
    var match_array := new seq<int>[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        match_array[i] := [];
        i := i + 1;
    }
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
    {
        var j := 1;
        while j <= n
            invariant 1 <= j <= n + 1
        {
            if j % i == 0 || i % j == 0 {
                match_array[i] := match_array[i] + [j];
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
    
    var ans := dfs_helper(1, n, match_array, vis, 0);
    result := ans;
}

method dfs_helper(pos: int, n: int, match_array: array<seq<int>>, vis: array<bool>, depth: int) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires match_array.Length == n + 1
    requires vis.Length == n + 1
    requires depth >= 0
    requires depth <= 15
    ensures count >= 0
    decreases 15 - depth
    modifies vis
{
    if pos == n + 1 {
        return 1;
    }
    
    if depth >= 15 {
        return 0;
    }
    
    count := 0;
    var i := 0;
    while i < |match_array[pos]|
        invariant 0 <= i <= |match_array[pos]|
        invariant count >= 0
    {
        var j := match_array[pos][i];
        if 1 <= j <= n && !vis[j] {
            vis[j] := true;
            var sub_count := dfs_helper(pos + 1, n, match_array, vis, depth + 1);
            count := count + sub_count;
            vis[j] := false;
        }
        i := i + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := integerReplacement_397(o);
    var o2 := getMoneyAmount_375(o1);
    var o3 := countTriples_1925(o2);
    
    // Ensure o3 is within bounds for smallestFactorization_625
    if o3 < 1 {
        o3 := 1;
    }
    if o3 > 2147483648 {
        o3 := 2147483648;
    }
    
    var o4 := smallestFactorization_625(o3);
    
    // Ensure o4 is within bounds for countArrangement_526
    if o4 < 1 {
        o4 := 1;
    }
    if o4 > 15 {
        o4 := 15;
    }
    
    var o5 := countArrangement_526(o4);
    result := o5;
}
