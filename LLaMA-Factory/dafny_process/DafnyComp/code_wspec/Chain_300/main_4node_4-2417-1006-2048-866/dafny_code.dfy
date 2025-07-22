
method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    // Count odd and even digits
    while t > 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant t >= 0
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
    
    // If odd number of digits, return next power of 10 plus balanced digits
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k / 2 == 0 then 0 else power10(k / 2) - 1;
        result := x + y;
        return;
    }
    
    // If equal number of odd and even digits, return n
    if a == b {
        result := n;
        return;
    }
    
    // Otherwise, recursively check n+1
    if n < 1000000000 {
        result := closestFair_2417(n + 1);
    } else {
        result := 1;
    }
}

function power10(k: int): int
    requires k >= 0
    ensures power10(k) >= 1
{
    if k == 0 then 1 else 10 * power10(k - 1)
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 1000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top * x];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top / x];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := sumSeq(stk);
    if result < 0 {
        result := 0;
    } else if result > 1000000 {
        result := 1000000;
    }
}

function sumSeq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sumSeq(s[1..])
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 100000000
    decreases *
{
    var x := n + 1;
    
    while x <= 100000000
        invariant x >= n + 1
        decreases 100000000 - x
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
        
        // Count digit frequencies
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            if 0 <= digit < 10 {
                cnt[digit] := cnt[digit] + 1;
            }
            y := y / 10;
        }
        
        // Check if beautiful number
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
    
    result := 1;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= 1
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        decreases *
    {
        if reverse(current) == current && isPrime(current) {
            result := current;
            return;
        }
        
        // Skip even-length palindromes between 10^7 and 10^8
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

function isPrime(x: int): bool
    requires x >= 0
{
    if x < 2 then false
    else isPrimeHelper(x, 2)
}

function isPrimeHelper(x: int, v: int): bool
    requires x >= 2 && v >= 2
    decreases x - v * v
{
    if v * v > x then true
    else if x % v == 0 then false
    else isPrimeHelper(x, v + 1)
}

function reverse(x: int): int
    requires x >= 0
{
    reverseHelper(x, 0)
}

function reverseHelper(x: int, acc: int): int
    requires x >= 0 && acc >= 0
    decreases x
{
    if x == 0 then acc
    else reverseHelper(x / 10, acc * 10 + x % 10)
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 1
    decreases *
{
    var o1 := closestFair_2417(o);
    var o2: int;
    if o1 <= 10000 {
        o2 := clumsy_1006(o1);
    } else {
        o2 := 0;
    }
    var o3: int;
    if o2 <= 1000000 {
        o3 := nextBeautifulNumber_2048(o2);
    } else {
        o3 := 1;
    }
    var o4 := primePalindrome_866(o3);
    result := o4;
}
