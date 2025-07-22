
method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 2 <= result <= 100000
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant ans >= 0
        invariant cnt >= 0
        invariant num >= 0
        decreases num
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            cnt := if cnt == 1 then 0 else 1;
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := if ans < 2 then 2 else (if ans > 100000 then 100000 else ans);
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 250
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 1
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i * i <= temp
            invariant i >= 2
            invariant s >= 0
            invariant temp >= 1
            decreases temp - i * i + 1
        {
            while temp % i == 0
                invariant temp >= 1
                invariant i >= 2
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
            result := if t >= 1 && t <= 250 then t else 1;
            return;
        }
        
        current := if s >= 1 && s <= 250 then s else 1;
        iterations := iterations + 1;
    }
    
    result := if current >= 1 && current <= 250 then current else 1;
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result
{
    var ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
        decreases n - a
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
            decreases n - b
        {
            var x := a * a + b * b;
            var c := 1;
            
            while c * c < x && c <= n
                invariant c >= 1
                invariant c <= n + 1
                decreases x - c * c
            {
                c := c + 1;
            }
            
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            
            b := b + 1;
        }
        a := a + 1;
    }
    
    result := if ans >= 1 then ans else 1;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num
    ensures 0 <= result <= 1000
{
    if num < 2 {
        result := num;
        return;
    }
    
    var ans := 0;
    var mul := 1;
    var n := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant ans >= 0
        invariant mul >= 1
        invariant n >= 1
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            mul := mul * 10;
            
            if mul > 100000000 {
                result := 0;
                return;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 1000 {
        result := ans;
    } else {
        result := 0;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    result := sum;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 100000
    ensures result >= 0
{
    var o1 := minOperations_2571(o);
    var o2 := smallestValue_2507(o1);
    var o3 := countTriples_1925(o2);
    var o4 := smallestFactorization_625(o3);
    var o5 := sumOfMultiples_2652(if o4 >= 1 && o4 <= 1000 then o4 else 1);
    result := o5;
}
