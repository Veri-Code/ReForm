
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := n;
    while m * m > n
        invariant 0 <= m
        decreases m
    {
        m := m - 1;
    }
    
    // Now m is floor(sqrt(n))
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall jj :: 0 <= jj < j ==> f[i, jj] == n + 1
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] == n + 1
        {
            f[i, j] := n + 1; // Use n+1 as "infinity"
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f[0, 0] == 0
        invariant forall ii, jj :: 0 <= ii <= m && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall jj :: 0 <= jj < j ==> 0 <= f[i, jj] <= n + 1
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
            invariant f[0, 0] == 0
            invariant forall jj :: 0 <= jj < j ==> f[i, jj] <= f[i-1, jj]
            invariant forall ii, jj :: 0 <= ii <= m && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
                var candidate := f[i, j - i * i] + 1;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result > n || result <= 0 {
        result := n;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 2
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000 // Bound iterations to ensure termination
        invariant current >= 1
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i <= temp / i && i <= temp && temp > 1
            invariant 2 <= i
            invariant s >= 0
            invariant temp >= 0
        {
            while temp % i == 0 && temp > 0
                invariant temp >= 0
                invariant s >= 0
                decreases temp
            {
                temp := temp / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            result := t;
            if result < 2 {
                result := 2;
            }
            return;
        }
        
        current := s;
        if current < 2 {
            current := 2;
        }
        iterations := iterations + 1;
    }
    
    // Fallback if we hit iteration limit
    result := current;
    if result < 2 {
        result := 2;
    }
}

method abs(x: int) returns (result: int)
    ensures result >= 0
    ensures result == x || result == -x
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures result >= 1
{
    var neg := num < 0;
    var absNum := abs(num);
    
    var cnt := new int[10];
    var k := 0;
    while k < 10
        invariant 0 <= k <= 10
        invariant forall i :: 0 <= i < k ==> cnt[i] == 0
    {
        cnt[k] := 0;
        k := k + 1;
    }
    
    var temp := absNum;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < 10 ==> cnt[i] >= 0
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
            invariant ans >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := -ans;
        if result < 1 {
            result := 1; // Ensure postcondition
        }
    } else {
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
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
        
        result := ans;
        if result < 1 {
            result := 1; // Ensure postcondition
        }
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= 0
{
    var current := n;
    var ans := 0;
    var iterations := 0;
    
    while current != 1 && iterations < 100
        invariant current >= 1
        invariant ans >= 0
        invariant iterations >= 0
        decreases 100 - iterations
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
        iterations := iterations + 1;
    }
    
    result := ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := numSquares_279(o);
    // o1 is between 1 and o, but we need it to be at least 2 for smallestValue_2507
    if o1 < 2 {
        o1 := 2;
    }
    var o2 := smallestValue_2507(o1);
    // o2 is at least 2, but we need to ensure it's within bounds for smallestNumber_2165
    if o2 > 1000000000000000 {
        o2 := 1000000000000000;
    }
    var o3 := smallestNumber_2165(o2);
    // o3 is at least 1, but we need to ensure it's within bounds for integerReplacement_397
    if o3 > 2147483648 {
        o3 := 2147483648;
    }
    var o4 := integerReplacement_397(o3);
    result := o4;
}
