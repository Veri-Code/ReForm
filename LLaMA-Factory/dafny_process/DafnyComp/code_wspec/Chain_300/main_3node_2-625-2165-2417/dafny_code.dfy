
method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures -1000000000000000 <= result <= 1000000000000000
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var n := num;
    
    var i := 9;
    while i >= 2
        invariant 1 <= i <= 9
        invariant n >= 1
        invariant mul >= 1
        invariant ans >= 0
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant mul >= 1
            invariant ans >= 0
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 {
        return ans;
    } else {
        return 0;
    }
}

method abs(num: int) returns (result: int)
    ensures result >= 0
    ensures result == if num >= 0 then num else -num
{
    if num >= 0 {
        return num;
    } else {
        return -num;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 1 <= result <= 1000000000
{
    var neg := num < 0;
    var n := abs(num);
    
    var cnt := new int[10];
    var j := 0;
    while j < 10
        invariant 0 <= j <= 10
        invariant forall k :: 0 <= k < j ==> cnt[k] == 0
    {
        cnt[j] := 0;
        j := j + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
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
            invariant ans >= 0
        {
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant ans >= 0
            {
                ans := ans * 10 + i;
                count := count + 1;
            }
            i := i - 1;
        }
        if ans == 0 {
            return 1;
        } else if ans <= 1000000000 {
            return ans;
        } else {
            return 1000000000;
        }
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
        invariant ans >= 0
    {
        var count := 0;
        while count < cnt[i]
            invariant 0 <= count <= cnt[i]
            invariant ans >= 0
        {
            ans := ans * 10 + i;
            count := count + 1;
        }
        i := i + 1;
    }
    
    if ans == 0 {
        return 1;
    } else if ans <= 1000000000 {
        return ans;
    } else {
        return 1000000000;
    }
}

method power10(k: int) returns (result: int)
    requires 0 <= k <= 10
    ensures result >= 1
{
    var res := 1;
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant res >= 1
    {
        res := res * 10;
        i := i + 1;
    }
    return res;
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    decreases 1000000000 - n + 1
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
    {
        var digit := t % 10;
        if digit % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        if k <= 10 {
            var x := power10(k);
            var half := k / 2;
            var y := 0;
            if half > 0 {
                var i := 0;
                while i < half
                    invariant 0 <= i <= half
                    invariant y >= 0
                {
                    y := y * 10 + 1;
                    i := i + 1;
                }
            }
            return x + y;
        } else {
            return 1000000000;
        }
    }
    
    if a == b {
        return n;
    }
    
    if n < 1000000000 {
        var next := closestFair_2417(n + 1);
        return next;
    } else {
        return n;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures result >= 1
{
    var o1 := smallestFactorization_625(o);
    var o2 := smallestNumber_2165(o1);
    var o3 := closestFair_2417(o2);
    return o3;
}
