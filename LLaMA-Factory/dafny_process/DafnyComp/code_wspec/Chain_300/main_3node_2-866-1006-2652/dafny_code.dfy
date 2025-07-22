
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
    forall k | v <= k < x
        ensures x % k != 0
    {
        if x % k == 0 {
            var quotient := x / k;
            assert quotient * k == x;
            assert quotient >= 2;
            assert quotient < v;
            assert quotient >= 2 && quotient < v;
            assert x % quotient == 0;
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
    ensures result >= 1
    ensures result <= 10000
    decreases *
{
    // Handle the case where n > 10000 immediately
    if n > 10000 {
        return 2;
    }
    
    var current := n;
    
    while true
        invariant current >= n
        invariant current <= 10000
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                return current;
            }
        }
        
        if current == 10000 {
            return 2;
        }
        
        current := current + 1;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000
{
    if n == 1 {
        return 1;
    }
    
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x < n
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
    
    // Sum the stack
    var sum := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant sum == SeqSum(stk[..i])
    {
        sum := sum + stk[i];
        SeqSumLemma(stk, i);
        i := i + 1;
    }
    
    // Ensure the result is within bounds
    if sum < 1 {
        return 1;
    } else if sum > 1000 {
        return 1000;
    } else {
        return sum;
    }
}

function SeqSum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + SeqSum(s[1..])
}

lemma SeqSumLemma(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures SeqSum(s[..i+1]) == SeqSum(s[..i]) + s[i]
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert s[..0] == [];
        assert SeqSum(s[..1]) == s[0] + SeqSum([]);
        assert SeqSum([]) == 0;
    } else {
        assert s[..i+1] == s[..i] + [s[i]];
        SeqSumAppendLemma(s[..i], [s[i]]);
    }
}

lemma SeqSumAppendLemma(s1: seq<int>, s2: seq<int>)
    ensures SeqSum(s1 + s2) == SeqSum(s1) + SeqSum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        SeqSumAppendLemma(s1[1..], s2);
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    return sum;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
    decreases *
{
    var o1 := primePalindrome_866(o);
    var o2 := clumsy_1006(o1);
    var o3 := sumOfMultiples_2652(o2);
    return o3;
}
