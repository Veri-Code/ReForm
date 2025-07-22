
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 1000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx == power10(n) - 1
        decreases a
    {
        // Create palindrome by mirroring a
        var b := a;
        var x := a;
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        // Check if x can be expressed as product of two numbers <= mx
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            invariant t <= mx
            decreases t
        {
            if x % t == 0 && x / t <= mx {
                var mod_result := x % 1337;
                if mod_result == 0 {
                    return 1000;
                } else if mod_result >= 1 && mod_result <= 1000 {
                    return mod_result;
                } else {
                    return 1;
                }
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 2147483647
{
    result := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result >= 0
        decreases n - i
    {
        if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
            result := result + i;
        }
        i := i + 1;
    }
    
    // Ensure result is at least 1 and within bounds
    if result == 0 {
        result := 1;
    } else if result > 2147483647 {
        result := 2147483647;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures result >= 0
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var remaining := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while remaining % i == 0 && remaining > 1
            invariant remaining >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases remaining
        {
            remaining := remaining / i;
            ans := mul * i + ans;
            mul := mul * 10;
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) >= 1
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else 100000000
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := sumOfMultiples_2652(o1);
    var o3 := smallestFactorization_625(o2);
    result := o3;
}
