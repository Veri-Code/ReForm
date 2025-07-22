
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 100000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx == power10(n) - 1
        decreases a
    {
        // Create palindrome by mirroring a
        var b := a;
        var x := a;
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        // Check if x can be expressed as product of two n-digit numbers
        var t := mx;
        while t * t >= x && t > mx / 10
            invariant t >= mx / 10
            invariant t <= mx
            decreases t
        {
            if x % t == 0 {
                var quotient := x / t;
                if quotient <= mx && quotient > mx / 10 {
                    var mod_result := x % 1337;
                    if mod_result == 0 {
                        return 1337;
                    } else {
                        return mod_result;
                    }
                }
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures -2147483648 <= result <= 2147483647
{
    var mod := 1000000007;
    var f := new int[n + 1];
    var i := 0;
    
    // Initialize array
    while i <= n
        invariant 0 <= i <= n + 1
        invariant f.Length == n + 1
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant f.Length == n + 1
        invariant f[0] == 1
        invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant f.Length == n + 1
        invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant f.Length == n + 1
            invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    var ans := f[n];
    assert 0 <= ans < mod;
    
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
        assert 0 <= ans < mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
        assert 0 <= ans < mod;
    }
    
    assert 0 <= ans < mod;
    assert mod == 1000000007;
    assert ans <= 1000000006;
    
    return ans;
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483647
    ensures -2147483648 <= result <= 2147483647
{
    var ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var temp := x;
    
    while temp != 0
        invariant -2147483648 <= temp <= 2147483647
        invariant -2147483648 <= ans <= 2147483647
        decreases if temp >= 0 then temp else -temp
    {
        // Check for overflow before multiplication
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := temp % 10;
        if temp < 0 && y > 0 {
            y := y - 10;
        }
        
        // Check bounds before assignment
        var new_ans := ans * 10 + y;
        if new_ans < mi || new_ans > mx {
            return 0;
        }
        
        ans := new_ans;
        temp := (temp - y) / 10;
    }
    
    return ans;
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) > 0
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else 100000000
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures -2147483648 <= result <= 2147483647
{
    var o1 := largestPalindrome_479(o);
    var o2 := numberOfWays_3183(o1);
    var o3 := reverse_7(o2);
    result := o3;
}
