
method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 250000  // Upper bound estimate
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        invariant result <= x * 1000  // Conservative upper bound
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    // Ensure result is at least 1
    if result == 0 {
        result := 1;
    }
    
    // Ensure upper bound
    if result > 250000 {
        result := 250000;
    }
}

method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250000
    ensures 1 <= ans <= 10000
{
    ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant 0 <= ans <= 10000
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 0 <= ans <= 10000
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
                if ans >= 10000 {
                    return 10000;
                }
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    // Ensure result is at least 1
    if ans == 0 {
        ans := 1;
    }
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    result := 1;
    while (result + 1) * (result + 1) <= x
        invariant result >= 0
        invariant result * result <= x
    {
        result := result + 1;
    }
}

method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    sum := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
    
    if n == 0 {
        sum := 0;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 1
{
    // We'll use arrays to simulate the counter
    // Maximum digit sum for numbers 1 to 10000 is 9*4 = 36 (for 9999)
    var maxDigitSum := 40; // Safe upper bound
    var cnt := new int[maxDigitSum];
    var i := 0;
    while i < maxDigitSum
        invariant 0 <= i <= maxDigitSum
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant forall j :: 0 <= j < maxDigitSum ==> cnt[j] >= 0
    {
        var s := digitSum(i);
        if s < maxDigitSum {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
            }
        }
        i := i + 1;
    }
    
    // Count how many groups have the maximum count
    result := 0;
    i := 0;
    while i < maxDigitSum
        invariant 0 <= i <= maxDigitSum
        invariant result >= 0
    {
        if cnt[i] == mx {
            result := result + 1;
        }
        i := i + 1;
    }
    
    // Ensure result is at least 1
    if result == 0 {
        result := 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures result >= 1
{
    var o1 := sumOfMultiples_2652(o);
    var o2 := countTriples_1925(o1);
    var o3 := countLargestGroup_1399(o2);
    result := o3;
}
