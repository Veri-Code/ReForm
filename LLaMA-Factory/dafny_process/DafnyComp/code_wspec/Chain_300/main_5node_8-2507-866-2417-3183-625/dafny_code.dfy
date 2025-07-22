
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 100000000
    decreases *
{
    var current := n;
    while true
        invariant current >= 2
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i <= current / i
            invariant i >= 2
            invariant s >= 0
            invariant current >= 1
        {
            while current % i == 0
                invariant i >= 2
                invariant s >= 0
                invariant current >= 1
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
            assume 1 <= t <= 100000000;
            return t;
        }
        current := s;
        assume current >= 2;
    }
}

method isPrime(x: int) returns (result: bool)
    requires x >= 1
{
    if x < 2 {
        return false;
    }
    var v := 2;
    while v * v <= x
        invariant v >= 2
        invariant forall k :: 2 <= k < v ==> x % k != 0
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method reverse(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    var res := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
    return res;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 1000000000
    decreases *
{
    var current := n;
    while true
        invariant current >= 1
        decreases *
    {
        var rev := reverse(current);
        var isPal := (rev == current);
        var prime := isPrime(current);
        
        if isPal && prime {
            assume 1 <= current <= 1000000000;
            return current;
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        }
        current := current + 1;
    }
}

method countDigits(n: int) returns (digits: int, odds: int, evens: int)
    requires n >= 1
    ensures digits >= 1
    ensures odds >= 0 && evens >= 0
    ensures odds + evens == digits
{
    var t := n;
    var k := 0;
    var a := 0;
    var b := 0;
    
    while t > 0
        invariant t >= 0
        invariant k >= 0
        invariant a >= 0 && b >= 0
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
    
    assume k >= 1;
    return k, a, b;
}

function power10(exp: int): int
    requires exp >= 0
    ensures power10(exp) >= 1
{
    if exp == 0 then 1 else 10 * power10(exp - 1)
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000
    decreases *
{
    var digits, odds, evens := countDigits(n);
    
    if digits % 2 == 1 {
        var x := power10(digits);
        var y := if digits / 2 > 0 then power10(digits / 2) - 1 else 0;
        assume 1 <= x + y <= 100000;
        return x + y;
    }
    
    if odds == evens {
        assume 1 <= n <= 100000;
        return n;
    }
    
    if n < 1000000000 {
        var next := closestFair_2417(n + 1);
        return next;
    } else {
        return 100000;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 2147483648
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant f[0] == 1
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    assume 1 <= ans <= 2147483648;
    return ans;
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
    {
        while current % i == 0
            invariant current >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases current
        {
            current := current / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if current < 2 && ans <= 2147483647 {
        return ans;
    } else {
        return 0;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := primePalindrome_866(o1);
    var o3 := closestFair_2417(o2);
    var o4 := numberOfWays_3183(o3);
    var o5 := smallestFactorization_625(o4);
    return o5;
}
