
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 250
    decreases *
{
    var current := n;
    
    while true
        invariant current >= 2
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i * i <= current
            invariant 2 <= i
            invariant s >= 0
            invariant current >= 1
        {
            while current % i == 0
                invariant current >= 1
                invariant i >= 2
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
            if t >= 1 && t <= 250 {
                return t;
            } else {
                return 1;
            }
        }
        current := s;
        
        // Safety check to ensure termination in practice
        if current > 250 {
            return 250;
        }
        
        // Ensure current stays >= 2 for the invariant
        if current < 2 {
            return 1;
        }
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 1000
{
    var ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    if ans == 0 {
        return 1;
    }
    if ans > 1000 {
        return 1000;
    }
    return ans;
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    var low := 1;
    var high := x;
    
    while low <= high
        invariant 1 <= low <= high + 1
        invariant (low - 1) * (low - 1) <= x
        invariant x < (high + 1) * (high + 1)
        decreases high - low
    {
        var mid := (low + high) / 2;
        if mid * mid == x {
            return mid;
        } else if mid * mid < x {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    return high;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 2147483648
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    if sum == 0 {
        return 1;
    }
    if sum > 2147483648 {
        return 2147483648;
    }
    return sum;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures result >= 0
{
    if num < 2 {
        return num;
    }
    
    var current := num;
    var ans := 0;
    var mul := 1;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant current >= 1
        invariant ans >= 0
        invariant mul >= 1
    {
        while current % i == 0
            invariant current >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases current
        {
            current := current / i;
            ans := mul * i + ans;
            mul := mul * 10;
            
            // Prevent overflow
            if mul > 100000000 || ans > 2000000000 {
                return 0;
            }
        }
        i := i - 1;
    }
    
    if current < 2 && ans <= 2147483647 {
        return ans;
    } else {
        return 0;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := countTriples_1925(o1);
    var o3 := sumOfMultiples_2652(o2);
    var o4 := smallestFactorization_625(o3);
    return o4;
}
