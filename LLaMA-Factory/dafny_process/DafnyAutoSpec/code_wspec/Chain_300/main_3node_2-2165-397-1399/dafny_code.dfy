
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 1 <= result <= 2147483648
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    
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
    
    // Handle zero case
    if n == 0 {
        cnt[0] := 1;
    } else {
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
    }
    
    var ans := 0;
    
    if neg {
        // For negative numbers, arrange digits in descending order
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant ans >= 0
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant ans >= 0
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                count := count + 1;
            }
            i := i - 1;
        }
        result := if ans == 0 then 1 else ans;
    } else {
        // For positive numbers, arrange digits in ascending order
        // But avoid leading zeros
        if cnt[0] > 0 {
            // Find first non-zero digit to put at front
            i := 1;
            while i < 10 && cnt[i] == 0
                invariant 1 <= i <= 10
                invariant forall j :: 1 <= j < i ==> cnt[j] == 0
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
            invariant ans >= 0
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var count := 0;
            while count < cnt[i]
                invariant 0 <= count <= cnt[i]
                invariant ans >= 0
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                count := count + 1;
            }
            i := i + 1;
        }
        
        result := if ans == 0 then 1 else ans;
    }
    
    // Ensure result is within bounds
    if result > 2147483648 {
        result := 2147483648;
    }
    if result < 1 {
        result := 1;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 0 <= result <= 10000
{
    var num := n;
    var ans := 0;
    
    while num != 1 && ans < 10000
        invariant num >= 1
        invariant ans >= 0
        invariant ans <= 10000
        decreases if num == 1 then 0 else 10000 - ans
    {
        if num % 2 == 0 {
            num := num / 2;
        } else if num != 3 && num % 4 == 3 {
            num := num + 1;
        } else {
            num := num - 1;
        }
        ans := ans + 1;
    }
    
    result := ans;
}

method digitSum(n: int) returns (sum: int)
    requires n >= 1
    ensures sum >= 1
{
    var num := n;
    sum := 0;
    
    while num > 0
        invariant num >= 0
        invariant sum >= 0
        decreases num
    {
        sum := sum + (num % 10);
        num := num / 10;
    }
    
    if sum == 0 {
        sum := 1; // This shouldn't happen for n >= 1, but ensures postcondition
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    // We'll use arrays to simulate the counter
    // Maximum digit sum for numbers 1 to 10000 is 9*4 = 36 (for 9999)
    var maxDigitSum := 36;
    var cnt := new int[maxDigitSum + 1];
    
    var i := 0;
    while i <= maxDigitSum
        invariant 0 <= i <= maxDigitSum + 1
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    var ans := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
    {
        var s := digitSum(i);
        if s <= maxDigitSum {
            cnt[s] := cnt[s] + 1;
            
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    result := if ans == 0 then 1 else ans;
}

method main_3node_2(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures 1 <= result
{
    var o1 := smallestNumber_2165(o);
    var o2 := integerReplacement_397(o1);
    if o2 >= 1 && o2 <= 10000 {
        var o3 := countLargestGroup_1399(o2);
        result := o3;
    } else {
        result := 1;
    }
}
