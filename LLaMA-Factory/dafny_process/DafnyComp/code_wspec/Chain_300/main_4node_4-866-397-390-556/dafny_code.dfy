
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

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 0
    decreases *
{
    var ans := 0;
    var current := n;
    
    while current != 1
        invariant current >= 1
        invariant ans >= 0
        decreases *
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

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n
    ensures 1 <= result
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant a1 >= 1
        invariant cnt * step <= n * 2
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                if an >= step {
                    an := an - step;
                }
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    return a1;
}

method digitToInt(c: char) returns (result: int)
    requires '0' <= c <= '9'
    ensures 0 <= result <= 9
{
    return (c as int) - ('0' as int);
}

method intToChar(n: int) returns (result: char)
    requires 0 <= n <= 9
    ensures '0' <= result <= '9'
{
    return (('0' as int) + n) as char;
}

method stringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
    {
        var digit := digitToInt(s[i]);
        res := res * 10 + digit;
        i := i + 1;
    }
    return res;
}

method intToString(n: int) returns (result: string)
    requires n >= 0
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
    if n == 0 {
        return "0";
    }
    
    var digits: seq<char> := [];
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| > 0
        decreases temp
    {
        var digit := temp % 10;
        var digitChar := intToChar(digit);
        digits := [digitChar] + digits;
        temp := temp / 10;
    }
    
    assert temp == 0;
    assert |digits| > 0;
    return digits;
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= -1
{
    var s := intToString(n);
    var cs := s;
    var len := |cs|;
    
    if len <= 1 {
        return -1;
    }
    
    var i := len - 2;
    
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i < len - 1
        decreases i + 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    var j := len - 1;
    while cs[i] >= cs[j]
        invariant i < j < len
        decreases j - i
    {
        j := j - 1;
    }
    
    var temp := cs[i];
    cs := cs[i := cs[j]];
    cs := cs[j := temp];
    
    var left := i + 1;
    var right := len - 1;
    while left < right
        invariant i + 1 <= left <= right + 1 <= len
        invariant forall k :: 0 <= k < |cs| ==> '0' <= cs[k] <= '9'
        invariant |cs| == len
        decreases right - left
    {
        temp := cs[left];
        cs := cs[left := cs[right]];
        cs := cs[right := temp];
        left := left + 1;
        right := right - 1;
    }
    
    var ans := stringToInt(cs);
    if ans > 2147483647 {
        return -1;
    } else {
        return ans;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= -1
    decreases *
{
    var o1 := primePalindrome_866(o);
    var o2 := integerReplacement_397(o1);
    if o2 >= 1 {
        var o3 := lastRemaining_390(o2);
        var o4 := nextGreaterElement_556(o3);
        return o4;
    } else {
        return -1;
    }
}
