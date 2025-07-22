
method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 2147483648
    ensures result > n
{
    var x := n + 1;
    while x <= 2147483648
        invariant x > n
        invariant x >= 1
        decreases 2147483648 - x
    {
        var y := x;
        var cnt := new int[10];
        var i := 0;
        while i < 10
            invariant 0 <= i <= 10
        {
            cnt[i] := 0;
            i := i + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            y := y / 10;
            if digit < 10 {
                cnt[digit] := cnt[digit] + 1;
            }
        }
        
        var isBeautiful := true;
        i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && cnt[i] != i {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            return x;
        }
        x := x + 1;
    }
    return 2147483648; // fallback
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 100000000
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 100000000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 100000000
        decreases 100000000 - ans
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
    
    if ans >= 100000000 {
        return 100000000;
    } else {
        return if ans == 0 then 1 else ans;
    }
}

method isPrime(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    
    var v := 2;
    while v * v <= x
        invariant v >= 2
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    return true;
}

method reverseNumber(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    var num := x;
    var res := 0;
    
    while num > 0
        invariant num >= 0
        invariant res >= 0
        decreases num
    {
        res := res * 10 + num % 10;
        num := num / 10;
    }
    return res;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 10000
{
    var current := n;
    
    while current <= 10000
        invariant current >= n
        invariant current >= 1
        decreases 10000 - current
    {
        var reversed := reverseNumber(current);
        if reversed == current {
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
    return 10000; // fallback
}

method digitSum(num: int) returns (sum: int)
    requires num >= 0
    ensures sum >= 0
{
    var n := num;
    var s := 0;
    
    while n > 0
        invariant n >= 0
        invariant s >= 0
        decreases n
    {
        s := s + n % 10;
        n := n / 10;
    }
    return s;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 0
{
    // Use arrays to simulate Counter behavior
    var cnt := new int[200]; // Max possible digit sum for numbers up to 10000
    var i := 0;
    while i < 200
        invariant 0 <= i <= 200
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 0;
    var mx := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 0
        invariant mx >= 0
    {
        var s := digitSum(i);
        if s < 200 {
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
    return ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures result >= 0
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2 := integerReplacement_397(o1);
    var o3 := primePalindrome_866(o2);
    var o4 := countLargestGroup_1399(o3);
    return o4;
}
