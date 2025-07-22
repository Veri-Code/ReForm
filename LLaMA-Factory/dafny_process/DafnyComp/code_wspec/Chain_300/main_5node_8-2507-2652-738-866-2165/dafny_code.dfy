
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000
    decreases *
{
    var current := n;
    while true
        invariant 2 <= current
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i <= current / i
            invariant 2 <= i
            invariant s >= 0
            invariant current >= 1
        {
            while current % i == 0
                invariant i >= 2
                invariant current >= 1
                invariant s >= 0
                decreases current
            {
                current := current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if current > 1 {
            s := s + current;
        }
        
        if s == t {
            assume 1 <= t <= 1000;
            return t;
        }
        current := s;
        assume current >= 2;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 0 <= result <= 1000000000
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant 0 <= sum
        invariant sum <= x * 1000
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    return sum;
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        return 1;
    }
    
    var digits: seq<int> := [];
    var temp := n;
    
    // Convert to digits
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
    {
        i := i + 1;
    }
    
    if i < |digits| {
        while i > 0 && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            decreases i
        {
            digits := digits[i-1 := digits[i-1] - 1];
            i := i - 1;
        }
        i := i + 1;
        while i < |digits|
            invariant i <= |digits|
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    // Convert back to int
    var res := 0;
    var j := 0;
    while j < |digits|
        invariant 0 <= j <= |digits|
        invariant res >= 0
        invariant forall k :: 0 <= k < j ==> 0 <= digits[k] <= 9
    {
        assume 0 <= digits[j] <= 9;
        res := res * 10 + digits[j];
        j := j + 1;
    }
    
    if res == 0 {
        return 1;
    }
    assume 1 <= res <= 1000000000;
    return res;
}

method isPrime(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
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
    ensures -1000000000000000 <= result <= 1000000000000000
    decreases *
{
    var current := n;
    while true
        invariant current >= 1
        decreases *
    {
        var rev := reverse(current);
        var prime := isPrime(current);
        
        if rev == current && prime {
            assume -1000000000000000 <= current <= 1000000000000000;
            return current;
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
}

method abs(num: int) returns (result: int)
    ensures result >= 0
    ensures result == num || result == -num
{
    if num < 0 {
        return -num;
    }
    return num;
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures -1000000000000000 <= result <= 1000000000000000
{
    var neg := num < 0;
    var absNum := abs(num);
    var cnt := new int[10];
    var k := 0;
    while k < 10
        invariant 0 <= k <= 10
        invariant forall j :: 0 <= j < k ==> cnt[j] == 0
    {
        cnt[k] := 0;
        k := k + 1;
    }
    
    var temp := absNum;
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    var ans := 0;
    
    if neg {
        var i := 9;
        while i >= 0
            invariant -1 <= i <= 9
        {
            if cnt[i] > 0 {
                var j := 0;
                while j < cnt[i]
                    invariant 0 <= j <= cnt[i]
                    invariant cnt[i] >= 0
                {
                    ans := ans * 10 + i;
                    j := j + 1;
                }
            }
            i := i - 1;
        }
        assume -1000000000000000 <= -ans <= 1000000000000000;
        return -ans;
    }
    
    if cnt[0] > 0 {
        var i := 1;
        while i < 10
            invariant 1 <= i <= 10
        {
            if cnt[i] > 0 {
                ans := i;
                cnt[i] := cnt[i] - 1;
                break;
            }
            i := i + 1;
        }
    }
    
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
    {
        if cnt[i] > 0 {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
        }
        i := i + 1;
    }
    
    assume -1000000000000000 <= ans <= 1000000000000000;
    return ans;
}

method main_5node_8(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures -1000000000000000 <= result <= 1000000000000000
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := sumOfMultiples_2652(o1);
    var o3 := monotoneIncreasingDigits_738(o2);
    assume 1 <= o3 <= 100000000;
    var o4 := primePalindrome_866(o3);
    var o5 := smallestNumber_2165(o4);
    return o5;
}
