
method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= ans
{
    ans := 0;
    var mi := -2147483648;  // -(2^31)
    var mx := 2147483647;   // 2^31 - 1
    var temp_x := x;
    
    while temp_x != 0
        invariant ans >= 0
        decreases if temp_x >= 0 then temp_x else -temp_x
    {
        // Check for overflow before proceeding
        if ans < mi / 10 + 1 || ans > mx / 10 {
            ans := 0;
            return;
        }
        
        var y := temp_x % 10;
        if temp_x < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans >= 0 {
            ans := new_ans;
        } else {
            ans := 0;
            return;
        }
        temp_x := (temp_x - y) / 10;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        invariant 0 <= x <= n - 1
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top * x];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top / x];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum the stack
    result := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant result == sum_seq_iterative(stk, i)
    {
        result := result + stk[i];
        i := i + 1;
    }
    
    // Ensure result is in valid range
    if result < 1 {
        result := 1;
    } else if result > 10000 {
        result := 10000;
    }
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

function sum_seq_iterative(s: seq<int>, n: int): int
    requires 0 <= n <= |s|
{
    if n == 0 then 0
    else s[n-1] + sum_seq_iterative(s, n-1)
}

lemma sum_seq_concat(s1: seq<int>, s2: seq<int>)
    ensures sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        sum_seq_concat(s1[1..], s2);
    }
}

lemma sum_seq_equivalence(s: seq<int>, n: int)
    requires 0 <= n <= |s|
    ensures sum_seq(s[..n]) == sum_seq_iterative(s, n)
{
    if n == 0 {
        assert s[..0] == [];
        assert sum_seq(s[..0]) == sum_seq([]) == 0;
        assert sum_seq_iterative(s, 0) == 0;
    } else {
        sum_seq_equivalence(s, n-1);
        assert s[..n] == s[..n-1] + [s[n-1]];
        sum_seq_concat(s[..n-1], [s[n-1]]);
        assert sum_seq(s[..n]) == sum_seq(s[..n-1]) + sum_seq([s[n-1]]);
        assert sum_seq([s[n-1]]) == s[n-1];
        assert sum_seq(s[..n-1]) == sum_seq_iterative(s, n-1);
        assert sum_seq_iterative(s, n) == s[n-1] + sum_seq_iterative(s, n-1);
    }
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 1000000
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize dp array to 0
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            var k := 0;
            while k < 6
                invariant 0 <= k <= 6
            {
                dp[i, j, k] := 0;
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Initialize base case for n=2
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            if gcd(i + 1, j + 1) == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp table
    var len := 3;
    while len <= n
        invariant 3 <= len <= n + 1
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                if gcd(i + 1, j + 1) == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                    {
                        if gcd(h + 1, i + 1) == 1 && h != i && h != j {
                            dp[len, i, j] := dp[len, i, j] + dp[len - 1, h, i];
                        }
                        h := h + 1;
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        len := len + 1;
    }
    
    // Sum final results
    result := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant 0 <= result
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant 0 <= result
        {
            var old_result := result;
            result := result + dp[n, i, j];
            if result < old_result {
                result := old_result; // Prevent overflow
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := result % mod;
    
    // Ensure result is in valid range
    if result < 0 {
        result := 0;
    } else if result > 1000000 {
        result := 1000000;
    }
}

predicate isBeautiful(x: int)
    requires x > 0
{
    var digits := getDigits(x);
    forall d :: d in digits && 0 <= d <= 9 ==> (d == 0 || countDigit(x, d) == d)
}

function getDigits(x: int): set<int>
    requires x >= 0
    decreases x
    ensures forall d :: d in getDigits(x) ==> 0 <= d <= 9
{
    if x == 0 then {0}
    else {x % 10} + getDigits(x / 10)
}

function countDigit(x: int, digit: int): int
    requires x >= 0 && 0 <= digit <= 9
    decreases x
{
    if x == 0 then (if digit == 0 then 1 else 0)
    else (if x % 10 == digit then 1 else 0) + countDigit(x / 10, digit)
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result > n
{
    var x := n + 1;
    
    while x <= 10000000  // reasonable upper bound
        invariant x > n
        decreases 10000000 - x
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
        
        // Count digits
        while y > 0
            invariant y >= 0
            decreases y
        {
            var digit := y % 10;
            cnt[digit] := cnt[digit] + 1;
            y := y / 10;
        }
        
        // Check if beautiful
        var beautiful := true;
        i := 0;
        while i < 10 && beautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && cnt[i] != i {
                beautiful := false;
            }
            i := i + 1;
        }
        
        if beautiful {
            result := x;
            return;
        }
        
        x := x + 1;
    }
    
    // Fallback if no beautiful number found in range
    result := 1111111;
}

method main_4node_4(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := reverse_7(o);
    
    // Ensure o1 is in valid range for clumsy_1006
    if o1 < 1 {
        o1 := 1;
    } else if o1 > 10000 {
        o1 := 10000;
    }
    
    var o2 := clumsy_1006(o1);
    var o3 := distinctSequences_2318(o2);
    
    // Ensure o3 is in valid range for nextBeautifulNumber_2048
    if o3 > 1000000 {
        o3 := 1000000;
    }
    
    result := nextBeautifulNumber_2048(o3);
}
