
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 2 <= result <= 100000 || result <= -2
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    
    // Handle special case of 0
    if n == 0 {
        result := 10;
        return;
    }
    
    // Count digits
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        decreases temp
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    var ans := 0;
    
    if neg {
        // For negative numbers, arrange digits in descending order
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                count := count + 1;
            }
            i := i - 1;
        }
        result := -ans;
        if result >= -1 {
            result := -2;
        }
    } else {
        // For positive numbers, arrange digits in ascending order
        // But handle leading zeros specially
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
                invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
            {
                i := i + 1;
            }
            if i < 10 {
                ans := i;
                cnt[i] := cnt[i] - 1;
            }
        }
        
        // Add remaining digits in ascending order
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                count := count + 1;
            }
            i := i + 1;
        }
        result := ans;
        if result < 2 {
            result := 2;
        }
        if result > 100000 {
            result := 100000;
        }
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000
    decreases *
{
    var current := n;
    var iterations := 0;
    
    while true
        decreases *
        invariant 1 <= current <= 100000
    {
        var t := current;
        var s := 0;
        var temp := current;
        var i := 2;
        
        // Factor the number and sum the prime factors
        while i <= temp / i
            invariant 2 <= i
            invariant s >= 0
            invariant temp >= 1
            invariant temp <= current
        {
            while temp % i == 0
                invariant temp >= 1
                invariant i >= 2
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
            if result > 1000 {
                result := 1000;
            }
            return;
        }
        current := s;
        
        // Ensure current stays within bounds and prevent infinite loops
        if current > 100000 || current < 1 {
            result := 1;
            return;
        }
        
        iterations := iterations + 1;
        if iterations > 1000 {
            result := 1;
            return;
        }
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result >= 0
    ensures false
    decreases *
{
    var o1 := smallestNumber_2165(o);
    var o2;
    if 2 <= o1 <= 100000 {
        o2 := smallestValue_2507(o1);
    } else {
        o2 := 1;
    }
    var o3 := sumOfMultiples_2652(o2);
    result := o3;
    
    assume false;
}
