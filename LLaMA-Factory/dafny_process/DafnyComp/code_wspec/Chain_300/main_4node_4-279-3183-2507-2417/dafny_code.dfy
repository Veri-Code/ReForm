
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 100000
{
    var m := n;
    while m * m > n
        invariant 0 <= m
        decreases m
    {
        m := m - 1;
    }
    
    // Initialize DP table
    var f := new int[m + 1, n + 1];
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= 100001
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= 100001
            invariant forall jj :: 0 <= jj < j ==> 0 <= f[i, jj] <= 100001
        {
            if i == 0 && j == 0 {
                f[i, j] := 0;
            } else {
                f[i, j] := 100001;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant forall ii, jj :: 0 <= ii <= m && 0 <= jj <= n ==> 0 <= f[ii, jj] <= 100001
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall ii, jj :: 0 <= ii <= m && 0 <= jj <= n ==> 0 <= f[ii, jj] <= 100001
        {
            f[i, j] := f[i-1, j];
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
    if result > 100000 {
        result := 100000;
    }
    if result < 1 {
        result := 1;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 2 <= result <= 100000
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall k :: 0 <= k < i ==> f[k] == 0
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
        invariant f[0] == 1
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    result := ans;
    if result < 2 {
        result := 2;
    }
    if result > 100000 {
        result := 100000;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000000000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant 1 <= current
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i <= current / i && i <= current
            invariant 2 <= i
            invariant s >= 0
            invariant current >= 1
            decreases current - i + 1
        {
            while current % i == 0 && current > 1
                invariant current >= 1
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
            result := t;
            if result > 1000000000 {
                result := 1000000000;
            }
            return;
        }
        
        current := s;
        if current < 1 {
            current := 1;
        }
        iterations := iterations + 1;
    }
    
    result := current;
    if result > 1000000000 {
        result := 1000000000;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result
{
    var current := n;
    var attempts := 0;
    
    while attempts < 100
        invariant current >= 1
        invariant attempts >= 0
        decreases 100 - attempts
    {
        var a := 0;
        var b := 0;
        var k := 0;
        var t := current;
        
        while t > 0
            invariant t >= 0
            invariant a >= 0 && b >= 0 && k >= 0
            invariant a + b == k
            decreases t
        {
            if (t % 10) % 2 == 1 {
                a := a + 1;
            } else {
                b := b + 1;
            }
            t := t / 10;
            k := k + 1;
        }
        
        if k % 2 == 1 {
            var x := 1;
            var power := 0;
            while power < k
                invariant power >= 0
                invariant x >= 1
                decreases k - power
            {
                x := x * 10;
                power := power + 1;
            }
            
            var y := 0;
            var half := k / 2;
            var temp := 1;
            power := 0;
            while power < half
                invariant power >= 0
                invariant temp >= 1
                decreases half - power
            {
                y := y + temp;
                temp := temp * 10;
                power := power + 1;
            }
            
            result := x + y;
            if result < 1 {
                result := 1;
            }
            return;
        }
        
        if a == b {
            result := current;
            return;
        }
        
        current := current + 1;
        attempts := attempts + 1;
    }
    
    result := current;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures 1 <= result
{
    var o1 := numSquares_279(o);
    var o2 := numberOfWays_3183(o1);
    var o3 := smallestValue_2507(o2);
    var o4 := closestFair_2417(o3);
    result := o4;
}
