
function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases if a < b then b else a
{
    if a == b then a
    else if a < b then gcd(a, b - a)
    else gcd(a - b, b)
}

function power10(k: int): int
    requires k >= 0
    ensures power10(k) > 0
{
    if k == 0 then 1 else 10 * power10(k - 1)
}

function countDigits(n: int): int
    requires n > 0
    ensures countDigits(n) > 0
    decreases n
{
    if n < 10 then 1 else 1 + countDigits(n / 10)
}

function countOddDigits(n: int): int
    requires n >= 0
    ensures countOddDigits(n) >= 0
    decreases n
{
    if n == 0 then 0
    else (if (n % 10) % 2 == 1 then 1 else 0) + countOddDigits(n / 10)
}

function countEvenDigits(n: int): int
    requires n >= 0
    ensures countEvenDigits(n) >= 0
    decreases n
{
    if n == 0 then 0
    else (if (n % 10) % 2 == 0 then 1 else 0) + countEvenDigits(n / 10)
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 10000
    decreases 1000000000 - n
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        decreases t
    {
        if (t % 10) % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k / 2 == 0 then 0 else power10(k / 2) - 1;
        result := x + y;
        if result > 10000 {
            result := 10000;
        }
    } else if a == b {
        result := n;
        if result > 10000 {
            result := 10000;
        }
    } else {
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 10000;
        }
    }
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 2 <= result <= 100000
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
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
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                if gcd(i + 1, j + 1) == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        if gcd(h + 1, i + 1) == 1 && h != i && h != j {
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
    decreases *
{
    var current := n;
    
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i <= current / i
            invariant i >= 2
            invariant s >= 0
            invariant current > 0
            decreases current - i * i + 1
        {
            while current % i == 0
                invariant i >= 2
                invariant current > 0
                decreases current
            {
                current := current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if current > 1 {
            s := s + current;
        }
        
        if s == t {
            result := t;
            return;
        }
        current := s;
        if current < 1 {
            current := 1;
        }
        if current > 100000 {
            result := 100000;
            return;
        }
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
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
            cnt := if cnt == 1 then 0 else 1;
        }
        current := current / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
    decreases *
{
    var o1 := closestFair_2417(o);
    var o2 := distinctSequences_2318(o1);
    var o3 := smallestValue_2507(o2);
    var o4 := minOperations_2571(o3);
    result := o4;
}
