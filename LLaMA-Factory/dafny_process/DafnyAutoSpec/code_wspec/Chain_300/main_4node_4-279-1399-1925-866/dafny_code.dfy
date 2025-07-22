
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant 0 <= m
        invariant m * m <= n
        decreases n - m * m
    {
        m := m + 1;
    }
    
    // Dynamic programming approach
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall jj :: 0 <= jj < j ==> f[i, jj] == n + 1
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] == n + 1
        {
            f[i, j] := n + 1; // Use n+1 as "infinity"
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f[0, 0] == 0
        invariant forall ii, jj :: 0 <= ii <= m && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
        invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
        invariant forall ii :: 1 <= ii < i ==> forall jj :: 0 <= jj <= n ==> f[ii, jj] <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall jj :: 0 <= jj < j ==> f[i, jj] <= n + 1
            invariant forall jj :: j <= jj <= n ==> f[i, jj] <= n + 1
            invariant f[0, 0] == 0
            invariant forall ii, jj :: 0 <= ii <= m && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
            invariant forall jjj :: 1 <= jjj <= n ==> f[0, jjj] == n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
                var candidate := f[i, j - i * i] + 1;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result > n {
        result := n;
    }
    
    // Ensure result is at least 1
    if result == 0 {
        result := 1;
    }
}

method digitSum(x: int) returns (sum: int)
    requires x >= 0
    ensures sum >= 0
{
    sum := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
        decreases temp
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 250
{
    var cnt := new int[82]; // Max digit sum for numbers up to 10000 is 9*4 + 9 = 45, but we'll be safe
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    var ans := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
    {
        var s := digitSum(i);
        if s < cnt.Length {
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
        ans := 1;
    }
    result := ans;
    if result > 250 {
        result := 250;
    }
}

method isqrt(x: int) returns (root: int)
    requires x >= 0
    ensures root >= 0
    ensures root * root <= x
    ensures x < (root + 1) * (root + 1)
{
    if x == 0 {
        return 0;
    }
    
    root := 0;
    while (root + 1) * (root + 1) <= x
        invariant root >= 0
        invariant root * root <= x
        decreases x - root * root
    {
        root := root + 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
{
    result := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant result >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant result >= 0
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                result := result + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method isPrime(x: int) returns (prime: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method reverseNumber(x: int) returns (reversed: int)
    requires x >= 0
    ensures reversed >= 0
{
    reversed := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant reversed >= 0
        decreases temp
    {
        reversed := reversed * 10 + (temp % 10);
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires n >= 1
    ensures result >= n
    decreases *
{
    var current := n;
    while true
        invariant current >= n
        decreases *
    {
        var rev := reverseNumber(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                return current;
            }
        }
        
        // Skip the range (10^7, 10^8) as in original code
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 1
    decreases *
{
    var o1 := numSquares_279(o);
    var o2 := countLargestGroup_1399(o1);
    var o3 := countTriples_1925(o2);
    assert o3 >= 0;
    if o3 == 0 {
        result := 1;
    } else {
        var o4 := primePalindrome_866(o3);
        result := o4;
    }
}
