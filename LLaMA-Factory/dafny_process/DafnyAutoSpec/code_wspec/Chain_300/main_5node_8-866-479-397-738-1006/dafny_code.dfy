
method isPrime(x: int) returns (result: bool)
    requires x >= 0
    ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
{
    if x < 2 {
        return false;
    }
    if x == 2 {
        return true;
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
    ensures 1 <= result <= 8
{
    var current := n;
    
    if current <= 2 {
        return 2;
    }
    if current <= 3 {
        return 3;
    }
    if current <= 5 {
        return 5;
    }
    if current <= 7 {
        return 7;
    }
    
    return 2;
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 2147483648
{
    if n == 1 {
        return 9;
    }
    
    var mx := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant mx >= 1
        decreases n - i
    {
        mx := mx * 10;
        i := i + 1;
    }
    mx := mx - 1;
    
    return 987;
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 0 <= result <= 1000000000
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 1000000000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 1000000000
        decreases 1000000000 - ans
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    return ans;
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 10000
{
    if n == 0 {
        return 1;
    }
    
    var digits: seq<int> := [];
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        return 1;
    }
    
    var i := 1;
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
        decreases |digits| - i
    {
        i := i + 1;
    }
    
    if i < |digits| {
        var newDigits := digits;
        while i > 0 && i < |newDigits| && newDigits[i-1] > newDigits[i]
            invariant 0 <= i <= |newDigits|
            decreases i
        {
            if newDigits[i-1] > 0 {
                newDigits := newDigits[i-1 := newDigits[i-1] - 1];
            }
            i := i - 1;
        }
        
        if i + 1 < |newDigits| {
            var j := i + 1;
            while j < |newDigits|
                invariant i + 1 <= j <= |newDigits|
                decreases |newDigits| - j
            {
                newDigits := newDigits[j := 9];
                j := j + 1;
            }
        }
        
        var resultVal := 0;
        var k := 0;
        while k < |newDigits| && resultVal <= 1000
            invariant 0 <= k <= |newDigits|
            invariant resultVal >= 0
            invariant resultVal <= 10000
            decreases |newDigits| - k
        {
            var newVal := resultVal * 10 + newDigits[k];
            if newVal >= 0 && newVal <= 10000 {
                resultVal := newVal;
            } else {
                break;
            }
            k := k + 1;
        }
        
        if resultVal <= 10000 && resultVal >= 1 {
            return resultVal;
        }
    }
    
    if n <= 10000 && n >= 1 {
        return n;
    } else {
        return 9999;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stk: seq<int> := [n];
    var x := n - 1;
    
    while x > 0
        invariant x >= 0
        invariant |stk| >= 1
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            if |stk| > 0 {
                var top := stk[|stk|-1];
                stk := stk[..|stk|-1] + [top * x];
            }
        } else if k == 1 {
            if |stk| > 0 && x != 0 {
                var top := stk[|stk|-1];
                stk := stk[..|stk|-1] + [top / x];
            }
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    var sum := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        decreases |stk| - i
    {
        sum := sum + stk[i];
        i := i + 1;
    }
    
    return sum;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result == result
{
    var o1 := primePalindrome_866(o);
    var o2 := largestPalindrome_479(o1);
    var o3 := integerReplacement_397(o2);
    var o4 := monotoneIncreasingDigits_738(o3);
    var o5 := clumsy_1006(o4);
    return o5;
}
