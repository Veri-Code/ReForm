
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
    
    // For any k where v <= k < x, if k divides x, then x/k < v
    // But x/k >= 2 (since k < x and k >= v >= 2), so x/k would be a divisor < v
    // This contradicts our invariant
    assert forall k :: v <= k < x ==> x % k != 0 by {
        forall k | v <= k < x
            ensures x % k != 0
        {
            if x % k == 0 {
                var quotient := x / k;
                assert quotient * k == x;
                assert quotient >= 2;
                assert quotient < v;
                assert x % quotient == 0;
                assert false;
            }
        }
    }
    
    return true;
}

method reverse(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    res := 0;
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= n
    ensures result >= 1
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        invariant current >= 1
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
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

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 1000000000
{
    if n == 1 {
        return 9;
    }
    
    var mx := pow10Method(n);
    mx := mx - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx >= 9
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
                assert x >= 1;
                assert x % 1337 >= 0;
                if x % 1337 == 0 {
                    return 1337;
                } else {
                    return x % 1337;
                }
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    return 9;
}

method pow10Method(n: int) returns (result: int)
    requires 0 <= n <= 10
    ensures result >= 1
    ensures n >= 2 ==> result >= 10
{
    result := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result >= 1
        invariant i >= 2 ==> result >= 10
    {
        result := result * 10;
        i := i + 1;
    }
}

method countDigits(n: int) returns (count: int, evenCount: int, oddCount: int)
    requires n >= 1
    ensures count >= 1
    ensures evenCount >= 0
    ensures oddCount >= 0
    ensures evenCount + oddCount == count
{
    count := 0;
    evenCount := 0;
    oddCount := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant count >= 0
        invariant evenCount >= 0
        invariant oddCount >= 0
        invariant evenCount + oddCount == count
        invariant temp == 0 ==> count >= 1
        decreases temp
    {
        var digit := temp % 10;
        if digit % 2 == 1 {
            oddCount := oddCount + 1;
        } else {
            evenCount := evenCount + 1;
        }
        count := count + 1;
        temp := temp / 10;
    }
    
    assert count >= 1;
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    decreases *
{
    var count, evenCount, oddCount := countDigits(n);
    
    if count % 2 == 1 {
        if count <= 10 {
            var x := pow10Method(count);
            var halfDigits := count / 2;
            var y;
            if halfDigits == 0 {
                y := 0;
            } else {
                var temp := pow10Method(halfDigits);
                y := (temp - 1) / 9;
            }
            result := x + y;
            return result;
        } else {
            return 1000000001;
        }
    }
    
    if evenCount == oddCount {
        return n;
    }
    
    if n < 1000000000 {
        var nextResult := closestFair_2417(n + 1);
        return nextResult;
    } else {
        return n;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 1
    decreases *
{
    var o1 := primePalindrome_866(o);
    assert o1 >= 1;
    
    var o1_bounded;
    if o1 <= 8 {
        o1_bounded := o1;
    } else {
        o1_bounded := 8;
    }
    
    var o2 := largestPalindrome_479(o1_bounded);
    var o3 := closestFair_2417(o2);
    result := o3;
}
