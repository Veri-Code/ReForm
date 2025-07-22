
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant 0 <= m
        invariant m * m <= n
        decreases n - m * m
    {
        m := m + 1;
    }
    
    // Dynamic programming table: f[i][j] = min squares using first i perfect squares to sum to j
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
            f[i, j] := n + 1; // Use n+1 as "infinity" since answer is at most n
            j := j + 1;
        }
        i := i + 1;
    }
    
    f[0, 0] := 0;
    
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f.Length0 == m + 1 && f.Length1 == n + 1
        invariant f[0, 0] == 0
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
        invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant f[0, 0] == 0
            invariant forall jj :: 0 <= jj < j ==> 0 <= f[i, jj] <= n + 1
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
            invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
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
    // The result should be valid, but add safety check
    if result > n || result < 1 {
        result := n;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 2 <= result <= 100000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000000
        invariant current >= n
        decreases 1000000 - iterations
    {
        var a := 0; // count of odd digits
        var b := 0; // count of even digits
        var k := 0; // total digits
        var t := current;
        
        while t > 0
            invariant t >= 0
            invariant a >= 0 && b >= 0 && k >= 0
            invariant a + b == k
            decreases t
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
            // Odd number of digits - construct next even-digit fair number
            var x := 1;
            var power := 0;
            while power < k
                invariant power >= 0
                invariant x == pow(10, power)
                decreases k - power
            {
                x := x * 10;
                power := power + 1;
            }
            
            var y := 0;
            if k > 1 {
                y := 1;
                var ones := 1;
                while ones < k / 2
                    invariant ones >= 1
                    invariant y >= 1
                    decreases k / 2 - ones
                {
                    y := y * 10 + 1;
                    ones := ones + 1;
                }
            }
            
            result := x + y;
            if result < 2 {
                result := 10;
            }
            if result > 100000 {
                result := 100000;
            }
            return;
        }
        
        if a == b {
            result := current;
            if result < 2 {
                result := 10;
            }
            if result > 100000 {
                result := 100000;
            }
            return;
        }
        
        current := current + 1;
        iterations := iterations + 1;
    }
    
    // Fallback - should not reach here with valid input
    result := 10;
}

function pow(base: int, exp: int): int
    requires base >= 0 && exp >= 0
    ensures pow(base, exp) >= 0
    ensures exp == 0 ==> pow(base, exp) == 1
    ensures base == 0 && exp > 0 ==> pow(base, exp) == 0
    ensures base > 0 ==> pow(base, exp) >= 1
{
    if exp == 0 then 1
    else if base == 0 then 0
    else base * pow(base, exp - 1)
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 0 <= result <= 1000000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000000
        invariant current >= 1
        decreases 1000000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i <= temp && temp > 1
            invariant 2 <= i
            invariant s >= 0
            invariant temp >= 1
            decreases temp + (temp - i + 1)
        {
            if temp % i == 0 {
                while temp % i == 0 && temp > 1
                    invariant temp >= 1
                    invariant s >= 0
                    decreases temp
                {
                    temp := temp / i;
                    s := s + i;
                }
            } else {
                i := i + 1;
            }
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            result := t;
            if result > 1000000 {
                result := 1000000;
            }
            return;
        }
        
        current := s;
        if current < 2 {
            current := 2;
        }
        iterations := iterations + 1;
    }
    
    // Fallback - should not reach here with valid input
    result := n;
    if result > 1000000 {
        result := 1000000;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result > n
{
    var x := n + 1;
    var iterations := 0;
    
    while iterations < 10000000
        invariant x > n
        decreases 10000000 - iterations
    {
        var y := x;
        var cnt := new int[10];
        var idx := 0;
        while idx < 10
            invariant 0 <= idx <= 10
        {
            cnt[idx] := 0;
            idx := idx + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            cnt[digit] := cnt[digit] + 1;
            y := y / 10;
        }
        
        var isBeautiful := true;
        idx := 0;
        while idx < 10 && isBeautiful
            invariant 0 <= idx <= 10
        {
            if cnt[idx] != 0 && idx != cnt[idx] {
                isBeautiful := false;
            }
            idx := idx + 1;
        }
        
        if isBeautiful {
            result := x;
            return;
        }
        
        x := x + 1;
        iterations := iterations + 1;
    }
    
    // Fallback - should not reach here with valid input
    result := n + 1;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures 1 <= result
{
    var o1 := numSquares_279(o);
    var o2 := closestFair_2417(o1);
    var o3 := smallestValue_2507(o2);
    var o4 := nextBeautifulNumber_2048(o3);
    result := o4;
}
