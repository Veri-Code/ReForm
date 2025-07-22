
function gcd(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd(b, a % b)
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 2147483648
{
    var x := n + 1;
    while x <= 2147483648
        invariant x >= n + 1
        decreases 2147483648 - x
    {
        var y := x;
        var cnt := new int[10];
        var i := 0;
        while i < 10
            invariant 0 <= i <= 10
        {
            cnt[i] := 0;
            i := i + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            cnt[digit] := cnt[digit] + 1;
            y := y / 10;
        }
        
        var isBeautiful := true;
        i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && i != cnt[i] {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            result := x;
            return;
        }
        x := x + 1;
    }
    result := 2147483648;
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 10000
{
    var num := n;
    var ans := 0;
    
    while num != 1 && ans < 10000
        invariant num >= 1
        invariant ans >= 0
        invariant ans <= 10000
        decreases 10000 - ans
    {
        if num % 2 == 0 {
            num := num / 2;
        } else if num != 3 && num % 4 == 3 {
            num := num + 1;
        } else {
            num := num - 1;
        }
        ans := ans + 1;
    }
    
    if ans >= 10000 {
        result := 10000;
    } else {
        result := ans + 1;
    }
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures -1000000000000000 <= result <= 1000000000000000
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
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
    
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant 0 <= ans < mod
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant 0 <= ans < mod
        {
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    result := ans;
}

method abs(x: int) returns (result: int)
    ensures result >= 0
    ensures result == x || result == -x
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 0 <= result <= 100000000
{
    var neg := num < 0;
    var absNum := abs(num);
    var cnt := new int[10];
    
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall k :: 0 <= k < i ==> cnt[k] >= 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := absNum;
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        decreases temp
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    var ans := 0;
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant ans >= 0
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
                invariant ans >= 0
            {
                if ans <= 10000000 {
                    ans := ans * 10 + i;
                }
                j := j + 1;
            }
            i := i - 1;
        }
        result := if ans <= 100000000 then ans else 100000000;
        return;
    }
    
    if cnt[0] > 0 {
        i := 1;
        while i < 10
            invariant 1 <= i <= 10
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        {
            if cnt[i] > 0 {
                ans := i;
                cnt[i] := cnt[i] - 1;
                break;
            }
            i := i + 1;
        }
    }
    
    i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant ans >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
    {
        var j := 0;
        while j < cnt[i]
            invariant 0 <= j <= cnt[i]
            invariant cnt[i] >= 0
            invariant ans >= 0
        {
            if ans <= 10000000 {
                ans := ans * 10 + i;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := if ans <= 100000000 then ans else 100000000;
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= 0
{
    if num == 0 {
        result := 0;
        return;
    }
    
    var digits := new int[20];
    var n := 0;
    var temp := num;
    
    while temp > 0 && n < 20
        invariant temp >= 0
        invariant n >= 0
        invariant n <= 20
        decreases temp
    {
        digits[n] := temp % 10;
        temp := temp / 10;
        n := n + 1;
    }
    
    var i := 0;
    while i < n / 2
        invariant 0 <= i <= n / 2
        invariant n <= 20
    {
        var tempDigit := digits[i];
        digits[i] := digits[n - 1 - i];
        digits[n - 1 - i] := tempDigit;
        i := i + 1;
    }
    
    var d := new int[20];
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant n <= 20
        invariant forall k :: 0 <= k < i ==> d[k] == k
    {
        d[i] := i;
        i := i + 1;
    }
    
    if n >= 2 {
        i := n - 2;
        while i >= 0
            invariant -1 <= i <= n - 2
            invariant n <= 20
            invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
        {
            if i + 1 < n && digits[i] <= digits[d[i + 1]] {
                d[i] := d[i + 1];
            }
            i := i - 1;
        }
    }
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant n <= 20
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        if i < n && d[i] < n && digits[i] < digits[d[i]] {
            var tempDigit := digits[i];
            digits[i] := digits[d[i]];
            digits[d[i]] := tempDigit;
            break;
        }
        i := i + 1;
    }
    
    result := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant n <= 20
        invariant result >= 0
    {
        var oldResult := result;
        if result <= 10000000 {
            result := result * 10 + digits[i];
        }
        if result < 0 || result > 100000000 {
            result := oldResult;
        }
        i := i + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures result >= 0
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2 := integerReplacement_397(o1);
    var o3 := distinctSequences_2318(o2);
    var o4 := smallestNumber_2165(o3);
    var o5 := maximumSwap_670(o4);
    result := o5;
}
