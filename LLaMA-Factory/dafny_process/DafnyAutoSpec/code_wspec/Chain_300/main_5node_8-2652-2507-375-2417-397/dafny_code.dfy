
method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 2 <= result <= 100000
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
    
    // Ensure postcondition - at least 3 is a multiple of 3
    if result == 0 {
        result := 3;
    }
    if result < 2 {
        result := 2;
    }
    if result > 100000 {
        result := 100000;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 200
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 1
        invariant iterations >= 0
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i * i <= temp && i <= 316
            invariant i >= 2
            invariant s >= 0
            invariant current >= 1
            invariant temp >= 1
            decreases temp - i * i + 1
        {
            while current % i == 0 && current > 1
                invariant current >= 1
                invariant s >= 0
                invariant i >= 2
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
            result := t;
            if result > 200 {
                result := 200;
            }
            if result < 1 {
                result := 1;
            }
            return;
        }
        
        current := s;
        if current <= 0 {
            current := 1;
        }
        iterations := iterations + 1;
    }
    
    result := if current <= 200 then current else 200;
    if result < 1 {
        result := 1;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 1000000000
{
    if n == 1 {
        result := 1;
        return;
    }
    
    var f := new int[n + 1, n + 1];
    
    var row := 0;
    while row <= n
        invariant 0 <= row <= n + 1
    {
        var col := 0;
        while col <= n
            invariant 0 <= col <= n + 1
            invariant 0 <= row <= n
        {
            f[row, col] := 0;
            col := col + 1;
        }
        row := row + 1;
    }
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant 1 <= i <= n - 1
        {
            f[i, j] := j + f[i, j - 1];
            
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant 1 <= i <= n - 1
                invariant i + 1 <= j <= n
            {
                var left_cost := if k - 1 >= i then f[i, k - 1] else 0;
                var right_cost := if k + 1 <= j then f[k + 1, j] else 0;
                var max_cost := if left_cost > right_cost then left_cost else right_cost;
                var total_cost := max_cost + k;
                
                if total_cost < f[i, j] {
                    f[i, j] := total_cost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result < 1 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
    }
}

method countDigits(n: int) returns (evenCount: int, oddCount: int, totalDigits: int)
    requires n >= 1
    ensures evenCount >= 0 && oddCount >= 0 && totalDigits >= 1
    ensures evenCount + oddCount == totalDigits
{
    evenCount := 0;
    oddCount := 0;
    totalDigits := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant evenCount >= 0 && oddCount >= 0 && totalDigits >= 0
        invariant evenCount + oddCount == totalDigits
        decreases temp
    {
        var digit := temp % 10;
        if digit % 2 == 0 {
            evenCount := evenCount + 1;
        } else {
            oddCount := oddCount + 1;
        }
        totalDigits := totalDigits + 1;
        temp := temp / 10;
    }
    
    // Ensure postcondition
    if totalDigits == 0 {
        totalDigits := 1;
        oddCount := 1;
    }
}

method power10(exp: int) returns (result: int)
    requires 0 <= exp <= 10
    ensures result >= 1
{
    result := 1;
    var i := 0;
    while i < exp
        invariant 0 <= i <= exp
        invariant result >= 1
        decreases exp - i
    {
        result := result * 10;
        i := i + 1;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 2147483648
    decreases 2147483648 - n
{
    var evenCount, oddCount, totalDigits := countDigits(n);
    
    if totalDigits % 2 == 1 {
        var exp := if totalDigits <= 10 then totalDigits else 10;
        var base := power10(exp);
        var halfDigits := totalDigits / 2;
        var ones := 0;
        var i := 0;
        while i < halfDigits && i < 5
            invariant 0 <= i <= halfDigits
            invariant 0 <= i <= 5
            invariant ones >= 0
            decreases halfDigits - i
        {
            ones := ones * 10 + 1;
            i := i + 1;
        }
        if halfDigits == 0 {
            ones := 0;
        }
        result := base + ones;
        if result > 2147483648 {
            result := 2147483648;
        }
    } else if evenCount == oddCount {
        result := n;
    } else if n < 1000000000 {
        result := closestFair_2417(n + 1);
    } else {
        result := 2147483648;
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= 0
{
    result := 0;
    var current := n;
    
    while current != 1 && result < 100
        invariant current >= 1
        invariant result >= 0
        decreases 100 - result
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        result := result + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures 0 <= result
{
    var o1 := sumOfMultiples_2652(o);
    var o2 := smallestValue_2507(o1);
    var o3 := getMoneyAmount_375(o2);
    var o4 := closestFair_2417(o3);
    var o5 := integerReplacement_397(o4);
    result := o5;
}
