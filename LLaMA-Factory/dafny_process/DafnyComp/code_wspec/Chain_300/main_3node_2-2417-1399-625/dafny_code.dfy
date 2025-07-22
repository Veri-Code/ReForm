
method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    decreases 1000000000 - n
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    // Count even and odd digits
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
    
    // If odd number of digits, need to go to next power of 10
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k >= 2 then power10(k / 2) else 0;
        result := x + y;
        return;
    }
    
    // If equal even and odd digits, return n
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

function power10(exp: int): int
    requires exp >= 0
    ensures power10(exp) >= 1
{
    if exp == 0 then 1
    else 10 * power10(exp - 1)
}

method digitSum(num: int) returns (sum: int)
    requires num >= 1
    ensures sum >= 1
{
    sum := 0;
    var i := num;
    while i > 0
        invariant i >= 0
        invariant sum >= 0
        decreases i
    {
        sum := sum + (i % 10);
        i := i / 10;
    }
    if sum == 0 { sum := 1; } // Ensure sum is at least 1
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var cnt := new int[46]; // Max digit sum for numbers up to 10000 is 9*5 = 45
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
    
    result := if ans > 0 then ans else 1;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures result >= 0
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var remaining := num;
    
    var i := 9;
    while i > 1
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant ans >= 0
        invariant mul >= 1
    {
        while remaining % i == 0 && mul <= 214748364 // Prevent overflow
            invariant remaining >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases remaining
        {
            remaining := remaining / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := closestFair_2417(o);
    var o2: int;
    if o1 <= 10000 {
        o2 := countLargestGroup_1399(o1);
    } else {
        o2 := 1;
    }
    var o3: int;
    if o2 <= 2147483648 {
        o3 := smallestFactorization_625(o2);
    } else {
        o3 := 0;
    }
    result := o3;
}
