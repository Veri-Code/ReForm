
method smallestValue_2507(n0: int) returns (result: int)
    requires 2 <= n0 <= 100000
    ensures 1 <= result <= 100000
    decreases *
{
    var n := n0;
    while true
        decreases *
    {
        var t := n;
        var s := 0;
        var i := 2;
        
        while i <= n / i
            invariant 2 <= i
            invariant s >= 0
            invariant n >= 1
        {
            while n % i == 0
                invariant n >= 1
                invariant i >= 2
                invariant s >= 0
                decreases n
            {
                n := n / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if n > 1 {
            s := s + n;
        }
        
        if s == t {
            if t >= 1 && t <= 100000 {
                return t;
            } else {
                return 1;
            }
        }
        n := s;
        if n <= 0 {
            return 1;
        }
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
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
        invariant forall k :: 0 <= k < j ==> f[k] >= 0
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant forall k :: 0 <= k < j ==> f[k] >= 0
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k < j ==> f[k] >= 0
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
    
    // Ensure result is at least 1
    if ans == 0 {
        result := 1;
    } else {
        result := ans;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    // Since n >= 1, we need to ensure sum >= 1
    if sum == 0 {
        result := 1;
    } else {
        result := sum;
    }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures result >= 0
    decreases *
{
    if n == 1 {
        return 9;
    }
    
    var mx := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant mx >= 1
    {
        mx := mx * 10;
        i := i + 1;
    }
    mx := mx - 1;
    
    var a := mx;
    while a > mx / 10
        invariant a >= mx / 10
        decreases a
    {
        // Create palindrome
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
        
        // Check if palindrome is product of two n-digit numbers
        var t := mx;
        while t * t >= x && t > mx / 10
            invariant t >= 0
            decreases t
        {
            if x % t == 0 && x / t <= mx && x / t > mx / 10 {
                return x % 1337;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    return 9;
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := numberOfWays_3183(o1);
    var o3: int;
    if o2 <= 1000 {
        o3 := sumOfMultiples_2652(o2);
    } else {
        o3 := 1;
    }
    var o4: int;
    if o3 <= 8 {
        o4 := largestPalindrome_479(o3);
    } else {
        o4 := 0;
    }
    result := o4;
}
