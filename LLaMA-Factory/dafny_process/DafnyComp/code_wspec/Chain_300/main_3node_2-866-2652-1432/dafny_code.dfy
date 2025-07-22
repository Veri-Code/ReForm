
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
    
    // Need to prove that checking up to sqrt(x) is sufficient
    assert forall k :: v <= k < x && k * k > x ==> x % k != 0 by {
        forall k | v <= k < x && k * k > x
            ensures x % k != 0
        {
            if x % k == 0 {
                assert x == k * (x / k);
                assert x / k >= 1;
                if x / k >= k {
                    assert x >= k * k;
                    assert false;
                } else {
                    assert x / k < k;
                    assert x / k >= 2;
                    assert x % (x / k) == 0;
                    assert 2 <= x / k < v;
                    assert false;
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
    ensures 1 <= result
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

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 0
    ensures result <= n * (n + 1) / 2
{
    var sum := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum >= 0
        invariant sum <= (i - 1) * i / 2
    {
        if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
            sum := sum + i;
        }
        i := i + 1;
    }
    
    return sum;
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
{
    var digits: seq<int> := [];
    var temp := num;
    
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        return 0;
    }
    
    var maxDigits := digits;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |maxDigits| == |digits|
        invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
    {
        if digits[i] != 9 {
            var j := 0;
            while j < |maxDigits|
                invariant 0 <= j <= |maxDigits|
                invariant |maxDigits| == |digits|
                invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
            {
                if maxDigits[j] == digits[i] {
                    maxDigits := maxDigits[j := 9];
                }
                j := j + 1;
            }
            break;
        }
        i := i + 1;
    }
    
    var minDigits := digits;
    if digits[0] != 1 {
        var j := 0;
        while j < |minDigits|
            invariant 0 <= j <= |minDigits|
            invariant |minDigits| == |digits|
            invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
        {
            if minDigits[j] == digits[0] {
                minDigits := minDigits[j := 1];
            }
            j := j + 1;
        }
    } else {
        i := 1;
        while i < |digits|
            invariant 1 <= i <= |digits|
            invariant |minDigits| == |digits|
            invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
        {
            if digits[i] != 0 && digits[i] != 1 {
                var j := 0;
                while j < |minDigits|
                    invariant 0 <= j <= |minDigits|
                    invariant |minDigits| == |digits|
                    invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
                {
                    if minDigits[j] == digits[i] {
                        minDigits := minDigits[j := 0];
                    }
                    j := j + 1;
                }
                break;
            }
            i := i + 1;
        }
    }
    
    var maxVal := 0;
    i := 0;
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
        invariant maxVal >= 0
    {
        maxVal := maxVal * 10 + maxDigits[i];
        i := i + 1;
    }
    
    var minVal := 0;
    i := 0;
    while i < |minDigits|
        invariant 0 <= i <= |minDigits|
        invariant minVal >= 0
    {
        minVal := minVal * 10 + minDigits[i];
        i := i + 1;
    }
    
    if maxVal >= minVal {
        return maxVal - minVal;
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
    var o2 := sumOfMultiples_2652(o1);
    assert o2 >= 0;
    if o2 > 100000000 {
        return 0;
    }
    if o2 == 0 {
        return 0;
    }
    var o3 := maxDiff_1432(o2);
    return o3;
}
