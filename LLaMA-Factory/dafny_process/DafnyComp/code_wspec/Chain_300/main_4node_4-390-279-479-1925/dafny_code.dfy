
method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= n
{
    var a1, an := 1, n;
    var i, step, cnt := 0, 1, n;
    
    while cnt > 1
        invariant 1 <= cnt <= n
        invariant step >= 1
        invariant i >= 0
        invariant step == power2(i)
        invariant a1 >= 1 - step && a1 <= n + step
        invariant an >= 1 - step && an <= n + step
        decreases cnt
    {
        if i % 2 == 1 {
            an := an - step;
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result < 1 { result := 1; }
    if result > n { result := n; }
}

function power2(n: int): int
    requires n >= 0
    ensures power2(n) >= 1
{
    if n == 0 then 1 else 2 * power2(n - 1)
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := sqrt_int(n);
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
            f[i, j] := n + 1;
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f[0, 0] == 0
        invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
        invariant forall ii, jj :: 1 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant f[0, 0] == 0
            invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
            invariant forall jj :: 0 <= jj < j ==> 0 <= f[i, jj] <= n + 1
            invariant forall ii, jj :: 1 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
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
    if result > n { result := n; }
    if result < 1 { result := 1; }
}

function sqrt_int(n: int): int
    requires n >= 0
    ensures sqrt_int(n) >= 0
    ensures sqrt_int(n) * sqrt_int(n) <= n
    ensures (sqrt_int(n) + 1) * (sqrt_int(n) + 1) > n
{
    if n == 0 then 0
    else sqrt_int_helper(n, 0, n + 1)
}

function sqrt_int_helper(n: int, low: int, high: int): int
    requires 0 < n
    requires 0 <= low < high
    requires low * low <= n
    requires high * high > n
    decreases high - low
    ensures sqrt_int_helper(n, low, high) >= 0
    ensures sqrt_int_helper(n, low, high) * sqrt_int_helper(n, low, high) <= n
    ensures (sqrt_int_helper(n, low, high) + 1) * (sqrt_int_helper(n, low, high) + 1) > n
{
    if low + 1 >= high then low
    else
        var mid := (low + high) / 2;
        if mid * mid <= n then
            sqrt_int_helper(n, mid, high)
        else
            sqrt_int_helper(n, low, mid)
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 1337
{
    if n == 1 {
        result := 9;
        return;
    }
    
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        decreases a
    {
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
        
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            decreases t
        {
            if x % t == 0 {
                result := x % 1337;
                if result == 0 { result := 1337; }
                return;
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    result := 9;
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) >= 1
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
            var c := sqrt_int(x);
            
            if c <= n && c * c == x {
                result := result + 1;
            }
            
            b := b + 1;
        }
        a := a + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := lastRemaining_390(o);
    var o2 := numSquares_279(if o1 <= 10000 then o1 else 10000);
    var o3 := largestPalindrome_479(if o2 <= 8 then o2 else 8);
    var o4 := countTriples_1925(if o3 <= 250 then o3 else 250);
    result := o4;
}
