
method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= result <= 1000000000
{
    var ans := 0;
    var mi := -2147483648;  // -(2^31)
    var mx := 2147483647;   // 2^31 - 1
    var temp := x;
    
    while temp != 0
        invariant ans >= 0
        invariant ans <= 1000000000
        decreases if temp >= 0 then temp else -temp
    {
        // Check for overflow before proceeding
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := temp % 10;
        if temp < 0 && y > 0 {
            y := y - 10;
        }
        
        var newAns := ans * 10 + y;
        if newAns < 0 || newAns > 1000000000 {
            return 0;
        }
        ans := newAns;
        temp := (temp - y) / 10;
    }
    
    return ans;
}

method countDigits(n: int) returns (count: int, evenCount: int, oddCount: int)
    requires n > 0
    ensures count > 0
    ensures evenCount >= 0 && oddCount >= 0
    ensures evenCount + oddCount == count
{
    var temp := n;
    count := 0;
    evenCount := 0;
    oddCount := 0;
    
    while temp > 0
        invariant evenCount >= 0 && oddCount >= 0
        invariant evenCount + oddCount == count
        invariant count >= 0
        invariant temp >= 0
        invariant temp == 0 ==> count > 0
        decreases temp
    {
        var digit := temp % 10;
        if digit % 2 == 1 {
            oddCount := oddCount + 1;
        } else {
            evenCount := evenCount + 1;
        }
        count := count + 1;
        temp := temp / 10;
    }
}

method power10(k: int) returns (result: int)
    requires 0 <= k <= 9
    ensures result > 0
    ensures result <= 1000000000
{
    result := 1;
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant result > 0
        invariant result <= 1000000000
        invariant result == power(10, i)
    {
        if result > 100000000 {
            result := 1000000000;
            return;
        }
        result := result * 10;
        i := i + 1;
    }
}

function power(base: int, exp: int): int
    requires base > 0 && exp >= 0
{
    if exp == 0 then 1 else base * power(base, exp - 1)
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000
    decreases 1000000000 - n
{
    var count, evenCount, oddCount := countDigits(n);
    
    if count % 2 == 1 {
        // Odd number of digits - need to go to next even-digit number
        if count <= 9 {
            var x := power10(count);
            var halfDigits := count / 2;
            var y := 0;
            if halfDigits > 0 && halfDigits <= 9 {
                y := power10(halfDigits - 1);
            }
            result := x + y;
            if result > 100000 {
                result := 100000;
            }
        } else {
            result := 100000;
        }
        return;
    }
    
    if evenCount == oddCount {
        if n <= 100000 {
            result := n;
        } else {
            result := 100000;
        }
        return;
    }
    
    if n + 1 <= 1000000000 {
        result := closestFair_2417(n + 1);
    } else {
        result := 100000;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
{
    var mod := 1000000007;
    var coins := [1, 2, 6];
    var f := new int[n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall k :: 0 <= k < i ==> f[k] == 0
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process each coin
    var coinIdx := 0;
    while coinIdx < 3
        invariant 0 <= coinIdx <= 3
        invariant f[0] == 1
        invariant forall k :: 0 <= k <= n ==> f[k] >= 0
    {
        var x := coins[coinIdx];
        var j := x;
        while j <= n
            invariant x <= j
            invariant f[0] == 1
            invariant forall k :: 0 <= k <= n ==> f[k] >= 0
            decreases n - j + 1
        {
            f[j] := (f[j] + f[j - x]) % mod;
            j := j + 1;
        }
        coinIdx := coinIdx + 1;
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    result := ans;
}

method main_3node_2(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := reverse_7(o);
    if o1 == 0 {
        result := numberOfWays_3183(1);
        return;
    }
    
    var o2 := closestFair_2417(o1);
    var o3 := numberOfWays_3183(o2);
    result := o3;
}
