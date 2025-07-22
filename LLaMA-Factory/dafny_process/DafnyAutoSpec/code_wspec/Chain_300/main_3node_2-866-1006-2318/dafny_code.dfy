
method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
    decreases *
{
    var o1 := primePalindrome_866(o);
    var o2 := clumsy_1006(o1);
    var o3 := distinctSequences_2318(o2);
    result := o3;
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 10000
    ensures isPalindrome(result)
    ensures isPrime(result)
    ensures result >= n || result == 2
    decreases *
{
    var current := n;
    while true
        invariant current >= 1
        decreases *
    {
        if isPalindrome(current) && isPrime(current) && current <= 10000 {
            if current >= n {
                return current;
            }
        }
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
        if current > 10000 {
            current := 2;
            return current;
        }
    }
}

function isPrime(x: int): bool
    requires x >= 0
{
    if x < 2 then false
    else forall k :: 2 <= k < x ==> x % k != 0
}

function isPalindrome(x: int): bool
    requires x >= 0
{
    x == reverseDigits(x)
}

function reverseDigits(x: int): int
    requires x >= 0
{
    if x == 0 then 0
    else reverseDigitsHelper(x, 0)
}

function reverseDigitsHelper(x: int, acc: int): int
    requires x >= 0
    requires acc >= 0
    decreases x
{
    if x == 0 then acc
    else reverseDigitsHelper(x / 10, acc * 10 + x % 10)
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant |stk| >= 1
        invariant k >= 0 && k <= 3
        invariant forall i :: 0 <= i < |stk| ==> stk[i] >= -100000000 && stk[i] <= 100000000
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var newVal := top * x;
            if newVal >= -100000000 && newVal <= 100000000 {
                stk := stk[..|stk| - 1] + [newVal];
            } else {
                stk := stk[..|stk| - 1] + [if newVal > 100000000 then 100000000 else -100000000];
            }
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
    
    var sum := sumArray(stk);
    if sum < 1 {
        result := 1;
    } else if sum > 10000 {
        result := 10000;
    } else {
        result := sum;
    }
}

function sumArray(arr: seq<int>): int
    requires |arr| >= 1
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= -100000000 && arr[i] <= 100000000
    ensures sumArray(arr) >= -100000000 * |arr| && sumArray(arr) <= 100000000 * |arr|
{
    if |arr| == 1 then arr[0]
    else arr[0] + sumArray(arr[1..])
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 0
{
    if n == 1 {
        return 6;
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
    
    // Fill base case for length 2
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
    
    // Fill dp table for lengths 3 to n
    var k := 3;
    while k <= n
        invariant 3 <= k <= n + 1
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
                            dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
                        }
                        h := h + 1;
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
    
    // Sum all possibilities for length n
    var ans := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant ans >= 0
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant ans >= 0
        {
            ans := (ans + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := ans;
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}
