
method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000
    decreases 1000000000 - n
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    // Count odd and even digits
    while t > 0
        invariant t >= 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        invariant k <= 10  // At most 10 digits for numbers up to 10^9
        invariant t == 0 ==> k >= 1  // At least one digit was processed
        invariant t > 0 ==> t < power10(10 - k)  // Remaining digits bound
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
    
    // If odd number of digits, construct next power of 10 + half 1's
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
        result := x + y;
        if result > 100000 {
            result := 100000;
        }
        return;
    }
    
    // If equal odd and even digits, return n
    if a == b {
        result := n;
        if result > 100000 {
            result := 100000;
        }
        return;
    }
    
    // Otherwise, recursively check n+1
    if n < 1000000000 {
        result := closestFair_2417(n + 1);
    } else {
        result := 100000;  // Fallback case
    }
}

function power10(k: int): int
    requires k >= 0
    ensures power10(k) >= 1
    ensures k <= 10 ==> power10(k) <= 10000000000
{
    if k == 0 then 1
    else if k == 1 then 10
    else if k == 2 then 100
    else if k == 3 then 1000
    else if k == 4 then 10000
    else if k == 5 then 100000
    else if k == 6 then 1000000
    else if k == 7 then 10000000
    else if k == 8 then 100000000
    else if k == 9 then 1000000000
    else 10000000000
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> f[j] == 0
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant f[0] == 1
        invariant forall j :: 1 <= j < i ==> f[j] >= 0 && f[j] < mod
    {
        f[i] := (f[i] + f[i - 1]) % mod;
        i := i + 1;
    }
    
    // Process coin 2
    i := 2;
    while i <= n
        invariant 2 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> f[j] >= 0 && f[j] < mod
    {
        f[i] := (f[i] + f[i - 2]) % mod;
        i := i + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        i := 6;
        while i <= n
            invariant 6 <= i <= n + 1
            invariant forall j :: 0 <= j < i ==> f[j] >= 0 && f[j] < mod
        {
            f[i] := (f[i] + f[i - 6]) % mod;
            i := i + 1;
        }
    }
    
    var ans := f[n];
    
    // Add special cases
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    result := ans;
}

method main_2node_1(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := closestFair_2417(o);
    var o2 := numberOfWays_3183(o1);
    result := o2;
}
