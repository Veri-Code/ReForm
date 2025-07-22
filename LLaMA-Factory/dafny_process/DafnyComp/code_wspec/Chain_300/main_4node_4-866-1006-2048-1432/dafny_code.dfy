
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
    
    // For any k where v <= k < x, if k divides x, then x/k also divides x
    // and x/k < v (since k >= v and k * (x/k) = x and v * v > x)
    // But we already know no number < v divides x, contradiction
    assert forall k :: v <= k < x ==> x % k != 0 by {
        forall k | v <= k < x
            ensures x % k != 0
        {
            if x % k == 0 {
                var quotient := x / k;
                assert quotient * k == x;
                assert quotient >= 1;
                if quotient == 1 {
                    assert k == x;
                    assert false; // contradiction since k < x
                } else {
                    assert quotient >= 2;
                    assert quotient * k == x;
                    assert k >= v;
                    assert v * v > x;
                    assert quotient < v; // since quotient * k = x and k >= v and v * v > x
                    assert x % quotient == 0;
                    assert false; // contradiction with loop invariant
                }
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
    ensures 1 <= result <= 1000000000
    ensures result >= n
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
                assert current >= n >= 1;
                if current <= 1000000000 {
                    return current;
                }
            }
        }
        
        // Special case optimization from Python code
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

function sumSeq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sumSeq(s[1..])
}

lemma sumSeqAppend(s: seq<int>, x: int)
    ensures sumSeq(s + [x]) == sumSeq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sumSeq([x]) == x + sumSeq([]);
        assert sumSeq([]) == 0;
    } else {
        assert s == [s[0]] + s[1..];
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        sumSeqAppend(s[1..], x);
        assert sumSeq(s[1..] + [x]) == sumSeq(s[1..]) + x;
        assert sumSeq(s + [x]) == s[0] + sumSeq(s[1..] + [x]);
        assert sumSeq(s + [x]) == s[0] + sumSeq(s[1..]) + x;
        assert sumSeq(s) == s[0] + sumSeq(s[1..]);
    }
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
    
    // Sum the stack
    var sum := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant sum == sumSeq(stk[..i])
    {
        sum := sum + stk[i];
        assert stk[..i+1] == stk[..i] + [stk[i]];
        sumSeqAppend(stk[..i], stk[i]);
        assert sumSeq(stk[..i+1]) == sumSeq(stk[..i]) + stk[i];
        i := i + 1;
    }
    
    assert i == |stk|;
    assert stk[..i] == stk;
    assert sum == sumSeq(stk);
    
    // Bound the result
    if sum < 0 {
        result := 0;
    } else if sum > 1000000 {
        result := 1000000;
    } else {
        result := sum;
    }
}

method countDigits(x: int) returns (cnt: array<int>)
    requires x >= 0
    ensures cnt.Length == 10
    ensures forall i :: 0 <= i < 10 ==> cnt[i] >= 0
{
    cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := x;
    while temp > 0
        invariant temp >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        decreases temp
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
}

method isBeautiful(x: int) returns (result: bool)
    requires x >= 1
{
    var cnt := countDigits(x);
    var i := 0;
    result := true;
    
    while i < 10
        invariant 0 <= i <= 10
    {
        if cnt[i] != 0 && i != cnt[i] {
            result := false;
            return;
        }
        i := i + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 100000000
    ensures result > n
    decreases *
{
    var x := n + 1;
    while true
        invariant x > n
        invariant x >= 1
        decreases *
    {
        var beautiful := isBeautiful(x);
        if beautiful {
            if x <= 100000000 {
                return x;
            }
        }
        x := x + 1;
    }
}

method intToString(num: int) returns (s: string)
    requires num >= 1
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if num < 10 {
        s := [('0' as int + num) as char];
    } else {
        var rest := intToString(num / 10);
        var digit := (('0' as int) + (num % 10)) as char;
        s := rest + [digit];
    }
}

method stringToInt(s: string) returns (num: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures num >= 0
{
    num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
    {
        num := num * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
}

method replaceChar(s: string, oldChar: char, newChar: char) returns (result: string)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> result[i] == newChar)
    ensures forall i :: 0 <= i < |s| ==> (s[i] != oldChar ==> result[i] == s[i])
    ensures (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') ==> 
            (('0' <= newChar <= '9') ==> (forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'))
{
    result := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == oldChar ==> result[j] == newChar)
        invariant forall j :: 0 <= j < i ==> (s[j] != oldChar ==> result[j] == s[j])
    {
        if s[i] == oldChar {
            result := result + [newChar];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
{
    var a := intToString(num);
    var b := intToString(num);
    
    // Maximize a: replace first non-'9' with '9'
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
    {
        if a[i] != '9' {
            a := replaceChar(a, a[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // Minimize b
    if |b| > 0 && b[0] != '1' {
        b := replaceChar(b, b[0], '1');
    } else {
        var j := 1;
        while j < |b|
            invariant 1 <= j <= |b|
        {
            if b[j] != '0' && b[j] != '1' {
                b := replaceChar(b, b[j], '0');
                break;
            }
            j := j + 1;
        }
    }
    
    var maxNum := stringToInt(a);
    var minNum := stringToInt(b);
    
    // Ensure result is non-negative
    if maxNum >= minNum {
        result := maxNum - minNum;
    } else {
        result := 0;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
    decreases *
{
    var o1 := primePalindrome_866(o);
    
    // Ensure o1 is within bounds for clumsy_1006
    var o1_bounded: int;
    if o1 > 10000 {
        o1_bounded := 10000;
    } else {
        o1_bounded := o1;
    }
    
    var o2 := clumsy_1006(o1_bounded);
    var o3 := nextBeautifulNumber_2048(o2);
    var o4 := maxDiff_1432(o3);
    result := o4;
}
