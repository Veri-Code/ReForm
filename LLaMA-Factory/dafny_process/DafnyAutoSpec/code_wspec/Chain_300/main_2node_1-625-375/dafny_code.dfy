
method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures 1 <= result <= 200 || result == 0
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var n := num;
    
    var i := 9;
    while i >= 2
        invariant 1 <= i <= 9
        invariant n >= 1
        invariant mul >= 1
        invariant ans >= 0
        invariant mul <= 10000000000  // 10^10 bound to prevent overflow
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant mul >= 1
            invariant ans >= 0
            invariant mul <= 10000000000
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            if mul <= 1000000000 {  // Only update mul if it won't overflow
                mul := mul * 10;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 && ans <= 200 {
        return ans;
    } else {
        return 0;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures result >= 0
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var row := 0;
    while row <= n
        invariant 0 <= row <= n + 1
        invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] == 0
    {
        var col := 0;
        while col <= n
            invariant 0 <= col <= n + 1
            invariant row <= n
            invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] == 0
            invariant forall c :: 0 <= c < col ==> f[row, c] == 0
        {
            f[row, col] := 0;
            col := col + 1;
        }
        row := row + 1;
    }
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
        invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
        decreases i
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant 1 <= i <= n - 1
            invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
        {
            f[i, j] := j + f[i, j - 1];
            
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant 1 <= i <= n - 1
                invariant i + 1 <= j <= n
                invariant f[i, j] >= 0
                invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
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
    
    return f[1, n];
}

method main_2node_1(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := smallestFactorization_625(o);
    
    if o1 == 0 {
        result := 0;
        return;
    }
    
    // Ensure o1 is in valid range for getMoneyAmount_375
    if o1 < 1 || o1 > 200 {
        result := 0;
        return;
    }
    
    var o2 := getMoneyAmount_375(o1);
    result := o2;
}
