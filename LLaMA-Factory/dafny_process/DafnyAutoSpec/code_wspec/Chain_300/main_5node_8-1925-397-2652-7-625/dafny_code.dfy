
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures ans >= 0
{
    ans := 0;
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
            var c := integerSquareRoot(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method integerSquareRoot(x: int) returns (root: int)
    requires x >= 0
    ensures root >= 0
    ensures root * root <= x < (root + 1) * (root + 1)
{
    if x == 0 {
        return 0;
    }
    
    root := 1;
    while root * root < x
        invariant root >= 1
        invariant (root - 1) * (root - 1) <= x
        decreases x - root * root
    {
        root := root + 1;
    }
    
    if root * root > x {
        root := root - 1;
    }
}

function decreaseMeasure(n: int): int
{
    if n % 2 == 0 then n
    else if n == 3 || n % 4 == 1 then n
    else n + 1
}

method integerReplacement_397(n: int) returns (ans: int)
    requires 1 <= n <= 2147483648
    ensures ans >= 0
{
    ans := 0;
    var current := n;
    
    while current != 1
        invariant current >= 1
        invariant ans >= 0
        decreases decreaseMeasure(current), if current % 2 == 0 then 0 else 1
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
        if ans > 1000 {
            break;
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

method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483647
    ensures ans >= 0
{
    ans := 0;
    var current := x;
    var mi := -2147483648;
    var mx := 2147483647;
    
    while current != 0
        invariant ans >= 0
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := current % 10;
        if current < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans < 0 {
            return 0;
        }
        ans := new_ans;
        current := (current - y) / 10;
    }
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures result >= 0
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var current := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant current >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
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
        }
        i := i - 1;
    }
    
    if current < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures result >= 0
{
    var o1 := countTriples_1925(o);
    
    // Bound o1 to valid range for integerReplacement_397
    if o1 > 2147483648 {
        o1 := 2147483648;
    }
    if o1 < 1 {
        o1 := 1;
    }
    
    var o2 := integerReplacement_397(o1);
    
    // Bound o2 to valid range for sumOfMultiples_2652
    if o2 > 1000 {
        o2 := 1000;
    }
    if o2 < 1 {
        o2 := 1;
    }
    
    var o3 := sumOfMultiples_2652(o2);
    
    // Bound o3 to valid range for reverse_7
    if o3 > 2147483647 {
        o3 := 2147483647;
    }
    if o3 < -2147483648 {
        o3 := -2147483648;
    }
    
    var o4 := reverse_7(o3);
    
    // Bound o4 to valid range for smallestFactorization_625
    if o4 > 2147483648 {
        o4 := 2147483648;
    }
    if o4 < 1 {
        o4 := 1;
    }
    
    var o5 := smallestFactorization_625(o4);
    result := o5;
}
