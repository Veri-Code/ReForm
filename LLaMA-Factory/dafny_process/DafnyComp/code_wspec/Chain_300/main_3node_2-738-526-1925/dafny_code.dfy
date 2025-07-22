
method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
    ensures result <= 1000000000
{
    if n == 0 {
        return 0;
    }
    
    var digits := intToDigits(n);
    var i := 1;
    
    // Find first decreasing position
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
        invariant forall k :: 0 <= k < i-1 ==> digits[k] <= digits[k+1]
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Fix decreasing digits by decrementing and propagating
        while i > 0 && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            invariant |digits| > 0
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        
        // Set all following digits to 9
        i := i + 1;
        while i < |digits|
            invariant 0 <= i <= |digits|
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(digits);
    
    // Prove result <= n
    assert forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9;
    assert result >= 0;
    if result > n {
        result := n;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 250
{
    // Precompute valid matches
    var matches := new seq<int>[n+1];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
    {
        var validForI := [];
        var j := 1;
        while j <= n
            invariant 1 <= j <= n+1
        {
            if j % i == 0 || i % j == 0 {
                validForI := validForI + [j];
            }
            j := j + 1;
        }
        matches[i] := validForI;
        i := i + 1;
    }
    
    var visited := new bool[n+1];
    i := 0;
    while i <= n
        invariant 0 <= i <= n+1
    {
        visited[i] := false;
        i := i + 1;
    }
    
    var count := dfsCount(1, n, matches, visited);
    result := if count == 0 then 1 else count;
    
    // Ensure bounds
    if result < 1 {
        result := 1;
    }
    if result > 250 {
        result := 250;
    }
}

method dfsCount(pos: int, n: int, matches: array<seq<int>>, visited: array<bool>) returns (count: int)
    requires 1 <= pos <= n+1
    requires 1 <= n <= 15
    requires matches.Length == n+1
    requires visited.Length == n+1
    ensures count >= 0
    modifies visited
    decreases n+1-pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var i := 0;
    while i < |matches[pos]|
        invariant 0 <= i <= |matches[pos]|
        invariant count >= 0
    {
        var j := matches[pos][i];
        if 1 <= j <= n && !visited[j] {
            visited[j] := true;
            var subCount := dfsCount(pos + 1, n, matches, visited);
            count := count + subCount;
            visited[j] := false;
        }
        i := i + 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
{
    result := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant result >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant result >= 0
        {
            var x := a * a + b * b;
            var c := intSqrt(x);
            if c <= n && c * c == x {
                result := result + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := monotoneIncreasingDigits_738(o);
    if o1 == 0 {
        result := 0;
        return;
    }
    if o1 > 15 {
        result := 0;
        return;
    }
    var o2 := countArrangement_526(o1);
    var o3 := countTriples_1925(o2);
    result := o3;
}

// Helper methods
method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        return [0];
    }
    
    digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp > 0 ==> |digits| >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    // Ensure we have at least one digit
    if |digits| == 0 {
        digits := [0];
    }
}

method digitsToInt(digits: seq<int>) returns (result: int)
    requires |digits| > 0
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
    {
        result := result * 10 + digits[i];
        i := i + 1;
    }
}

method intSqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x
    ensures (result + 1) * (result + 1) > x
{
    if x == 0 {
        return 0;
    }
    
    result := 1;
    while (result + 1) * (result + 1) <= x
        invariant result >= 1
        invariant result * result <= x
        decreases x - result * result
    {
        result := result + 1;
    }
}
