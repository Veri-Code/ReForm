
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 2
    decreases *
{
    var current := n;
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        // Factor current and sum the prime factors
        while i * i <= temp
            invariant 2 <= i
            invariant s >= 0
            invariant temp >= 0
        {
            while temp % i == 0 && temp > 0
                invariant temp >= 0
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
            if t >= 2 {
                return t;
            } else {
                return 2;
            }
        }
        current := s;
        if s < 2 {
            return 2;
        }
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
    ensures result <= 1000000000
{
    if n == 0 {
        return 0;
    }
    
    // Convert to sequence of digits
    var digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        return 0;
    }
    
    // Find first decreasing position
    var i := 1;
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Make monotone by decreasing and setting 9s
        while i > 0 && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            invariant |digits| > 0
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        while i < |digits|
            invariant 0 <= i <= |digits|
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    // Convert back to integer
    result := 0;
    var multiplier := 1;
    i := |digits| - 1;
    while i >= 0
        invariant -1 <= i < |digits|
        invariant result >= 0
        invariant multiplier >= 1
        decreases i
    {
        if digits[i] >= 0 {
            result := result + digits[i] * multiplier;
        }
        multiplier := multiplier * 10;
        i := i - 1;
    }
    
    if result > n {
        result := n;
    }
}

method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant m >= 0
        invariant m * m <= n
    {
        m := m + 1;
    }
    
    // DP table: f[i][j] = min squares using first i perfect squares to sum to j
    var f := new int[m + 1, n + 1];
    
    // Initialize
    var j := 0;
    while j <= n
        invariant 0 <= j <= n + 1
    {
        if j == 0 {
            f[0, j] := 0;
        } else {
            f[0, j] := n + 1; // Large value representing infinity
        }
        j := j + 1;
    }
    
    var i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
    {
        j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant 1 <= i <= m
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i && f[i, j - i * i] + 1 < f[i, j] {
                f[i, j] := f[i, j - i * i] + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result <= 0 || result > n {
        result := 1;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    // Initialize
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        if i == 0 {
            f[i] := 1;
        } else {
            f[i] := 0;
        }
        i := i + 1;
    }
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
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
    if result < 0 {
        result := 0;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    
    // Ensure o1 is within bounds for monotoneIncreasingDigits_738
    if o1 > 1000000000 {
        o1 := 1000000000;
    }
    var o2 := monotoneIncreasingDigits_738(o1);
    
    // Ensure o2 is within bounds for numSquares_279
    if o2 < 1 {
        o2 := 1;
    }
    if o2 > 10000 {
        o2 := 10000;
    }
    var o3 := numSquares_279(o2);
    
    // Ensure o3 is within bounds for numberOfWays_3183
    if o3 > 100000 {
        o3 := 100000;
    }
    var o4 := numberOfWays_3183(o3);
    result := o4;
}
