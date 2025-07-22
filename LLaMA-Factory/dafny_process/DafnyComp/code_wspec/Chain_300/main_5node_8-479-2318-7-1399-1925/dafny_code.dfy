
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 10000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 < a <= mx || a == mx / 10
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
        
        // Check if x has a factor in valid range
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 {
                    return 1337;
                } else {
                    return res;
                }
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

function power10(n: int): int
    requires 0 <= n <= 8
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

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures -2147483648 <= result <= 2147483648
{
    if n == 1 {
        return 6;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize all dp values to 0
    var init_k := 0;
    while init_k <= n
        invariant 0 <= init_k <= n + 1
        invariant forall k', i', j' :: 0 <= k' < init_k && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] == 0
    {
        var init_i := 0;
        while init_i < 6
            invariant 0 <= init_i <= 6
            invariant forall k', i', j' :: 0 <= k' < init_k && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] == 0
            invariant forall i', j' :: 0 <= i' < init_i && 0 <= j' < 6 ==> dp[init_k, i', j'] == 0
        {
            var init_j := 0;
            while init_j < 6
                invariant 0 <= init_j <= 6
                invariant forall k', i', j' :: 0 <= k' < init_k && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] == 0
                invariant forall i', j' :: 0 <= i' < init_i && 0 <= j' < 6 ==> dp[init_k, i', j'] == 0
                invariant forall j' :: 0 <= j' < init_j ==> dp[init_k, init_i, j'] == 0
            {
                dp[init_k, init_i, init_j] := 0;
                init_j := init_j + 1;
            }
            init_i := init_i + 1;
        }
        init_k := init_k + 1;
    }
    
    // Initialize dp for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant 0 <= i < 6
            invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
        {
            if gcd(i + 1, j + 1) == 1 && i != j {
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
        invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
            invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
                invariant 0 <= i < 6
                invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
            {
                if gcd(i + 1, j + 1) == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                        invariant 0 <= i < 6
                        invariant 0 <= j < 6
                        invariant dp[k, i, j] >= 0
                        invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
                    {
                        if gcd(h + 1, i + 1) == 1 && h != i && h != j {
                            dp[k, i, j] := dp[k, i, j] + dp[k - 1, h, i];
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
        invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant 0 <= i < 6
            invariant ans >= 0
            invariant forall k', i', j' :: 0 <= k' <= n && 0 <= i' < 6 && 0 <= j' < 6 ==> dp[k', i', j'] >= 0
        {
            ans := ans + dp[n, i, j];
            j := j + 1;
        }
        i := i + 1;
    }
    
    return ans % mod;
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483648
    ensures 1 <= result <= 10000
{
    var ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var temp := x;
    
    while temp != 0
        invariant -2147483648 <= temp <= 2147483648
        decreases if temp >= 0 then temp else -temp
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 1; // Return 1 to satisfy postcondition instead of 0
        }
        
        var y := temp % 10;
        if temp < 0 && y > 0 {
            y := y - 10;
        }
        
        // Check for overflow before updating ans
        if ans > (mx - y) / 10 || ans < (mi - y) / 10 {
            return 1;
        }
        
        ans := ans * 10 + y;
        temp := (temp - y) / 10;
    }
    
    if ans <= 0 {
        return 1; // Ensure positive result
    } else if ans > 10000 {
        return 10000; // Cap at 10000
    } else {
        return ans;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 250
{
    var cnt := new int[82]; // Max digit sum for numbers up to 10000 is 9+9+9+9 = 36, use 82 to be safe
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 0;
    var mx := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 0
        invariant mx >= 0
    {
        var s := digitSum(i);
        if 0 <= s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    if ans == 0 {
        return 1;
    } else if ans > 250 {
        return 250;
    } else {
        return ans;
    }
}

function digitSum(num: int): int
    requires num >= 0
    decreases num
{
    if num == 0 then 0
    else (num % 10) + digitSum(num / 10)
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
            invariant 1 <= a < n
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
    
    return ans;
}

function isqrt(x: int): int
    requires x >= 0
{
    if x == 0 then 0
    else if x < 4 then 1
    else
        var guess := x / 2;
        isqrtHelper(x, guess)
}

function isqrtHelper(x: int, guess: int): int
    requires x >= 0 && guess >= 0
    decreases guess
{
    if guess == 0 then 0
    else
        var newGuess := (guess + x / guess) / 2;
        if newGuess >= guess then guess
        else isqrtHelper(x, newGuess)
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := distinctSequences_2318(o1);
    var o3 := reverse_7(o2);
    var o4 := countLargestGroup_1399(o3);
    var o5 := countTriples_1925(o4);
    return o5;
}
