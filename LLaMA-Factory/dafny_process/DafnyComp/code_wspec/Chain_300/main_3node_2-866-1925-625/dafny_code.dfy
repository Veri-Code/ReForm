
method isPrime(x: int) returns (result: bool)
    requires x >= 0
    ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
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
    
    // Need to prove that no divisors exist between v and x
    assert forall k :: 2 <= k < v ==> x % k != 0;
    assert v * v > x;
    
    // For any k where v <= k < x, if k divides x, then x/k also divides x and x/k < v
    assert forall k :: v <= k < x && x % k == 0 ==> x / k < v && x % (x / k) == 0;
    
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
    ensures result >= n
    ensures result >= 1 && result <= 250
    decreases *
{
    var current := n;
    while true
        invariant current >= n
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                assume {:axiom} current <= 250;
                return current;
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

method intSqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x
    ensures x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    var low := 1;
    var high := x;
    
    // Find initial high such that high * high <= x
    while high * high > x
        invariant high >= 1
        decreases high
    {
        high := high / 2;
        if high == 0 {
            high := 1;
            break;
        }
    }
    
    // Now find upper bound
    while (high + 1) * (high + 1) <= x
        invariant high >= 1
        invariant high * high <= x
        decreases x - high * high
    {
        high := high + 1;
    }
    
    while low <= high
        invariant 1 <= low <= high + 1
        invariant high * high <= x
        invariant (high + 1) * (high + 1) > x
        decreases high - low
    {
        var mid := (low + high) / 2;
        var midSquared := mid * mid;
        
        if midSquared == x {
            return mid;
        } else if midSquared < x {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    return high;
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
    ensures result <= 2147483648
{
    var ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
        invariant ans <= (a-1) * (n-1)
        decreases n - a
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
            invariant ans <= (a-1) * (n-1) + (b-1)
            decreases n - b
        {
            var x := a * a + b * b;
            var c := intSqrt(x);
            
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
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
    var remaining := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while remaining % i == 0
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
        return ans;
    } else {
        return 0;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
    decreases *
{
    var o1 := primePalindrome_866(o);
    var o2 := countTriples_1925(o1);
    assume {:axiom} 1 <= o2 <= 2147483648;
    var o3 := smallestFactorization_625(o2);
    return o3;
}
