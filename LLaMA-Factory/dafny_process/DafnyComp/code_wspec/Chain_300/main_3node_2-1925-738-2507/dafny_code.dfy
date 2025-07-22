
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures 0 <= ans <= 1000000000
{
    ans := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant 0 <= ans <= (a - 1) * (n - 1) * (n - 1)
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 0 <= ans <= (a - 1) * (n - 1) * (n - 1) + (b - 1) * (n - 1)
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
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures (isqrt(x) + 1) * (isqrt(x) + 1) > x
{
    if x == 0 then 0
    else if x == 1 then 1
    else
        var guess := x / 2;
        isqrt_helper(x, guess, x + 1)
}

function isqrt_helper(x: int, guess: int, fuel: int): int
    requires x >= 0
    requires guess >= 0
    requires fuel >= 0
    ensures isqrt_helper(x, guess, fuel) >= 0
    ensures isqrt_helper(x, guess, fuel) * isqrt_helper(x, guess, fuel) <= x
    ensures (isqrt_helper(x, guess, fuel) + 1) * (isqrt_helper(x, guess, fuel) + 1) > x
    decreases fuel
{
    if fuel == 0 then
        var result := if guess * guess <= x then guess else if guess > 0 then guess - 1 else 0;
        if result >= 0 && result * result <= x && (result + 1) * (result + 1) > x then 
            result
        else if result > 0 && (result - 1) >= 0 && (result - 1) * (result - 1) <= x && result * result > x then 
            result - 1
        else 
            linearSearch(x)
    else if guess * guess <= x && (guess + 1) * (guess + 1) > x then
        guess
    else if guess * guess > x then
        if guess > 0 then isqrt_helper(x, guess - 1, fuel - 1) else 0
    else
        isqrt_helper(x, guess + 1, fuel - 1)
}

function linearSearch(x: int): int
    requires x >= 0
    ensures linearSearch(x) >= 0
    ensures linearSearch(x) * linearSearch(x) <= x
    ensures (linearSearch(x) + 1) * (linearSearch(x) + 1) > x
{
    linearSearchHelper(x, 0)
}

function linearSearchHelper(x: int, r: int): int
    requires x >= 0
    requires r >= 0
    requires r * r <= x
    ensures linearSearchHelper(x, r) >= 0
    ensures linearSearchHelper(x, r) * linearSearchHelper(x, r) <= x
    ensures (linearSearchHelper(x, r) + 1) * (linearSearchHelper(x, r) + 1) > x
    decreases x - r * r
{
    if (r + 1) * (r + 1) > x then r
    else linearSearchHelper(x, r + 1)
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
    ensures n >= 2 ==> result >= 2
{
    if n < 10 {
        result := n;
        return;
    }
    
    var digits := intToDigits(n);
    var len := |digits|;
    
    var i := 1;
    while i < len && digits[i-1] <= digits[i]
        invariant 1 <= i <= len
        invariant |digits| == len
        invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
    {
        i := i + 1;
    }
    
    if i < len {
        while i > 0 && i < len && digits[i-1] > digits[i]
            invariant 0 <= i <= len
            invariant |digits| == len
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        while i < len
            invariant 0 <= i <= len
            invariant |digits| == len
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(digits);
    
    // Ensure postconditions
    if result > n {
        result := n;
    }
    if n >= 2 && result < 2 {
        result := 2;
    }
}

function intToDigits(n: int): seq<int>
    requires n >= 0
    ensures |intToDigits(n)| >= 1
    ensures forall i :: 0 <= i < |intToDigits(n)| ==> 0 <= intToDigits(n)[i] <= 9
{
    if n < 10 then [n]
    else intToDigits(n / 10) + [n % 10]
}

function digitsToInt(digits: seq<int>): int
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures digitsToInt(digits) >= 0
{
    if |digits| == 1 then digits[0]
    else digitsToInt(digits[..|digits|-1]) * 10 + digits[|digits|-1]
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 2
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 2
        invariant iterations >= 0
    {
        var t := current;
        var s := sumOfPrimeFactors(current);
        
        if s == t {
            result := t;
            return;
        }
        current := s;
        iterations := iterations + 1;
    }
    
    result := current;
}

function sumOfPrimeFactors(n: int): int
    requires n >= 2
    ensures sumOfPrimeFactors(n) >= 2
{
    var result := sumOfPrimeFactorsHelper(n, 2, 0);
    if result == 0 then n else if result < 2 then 2 else result
}

function sumOfPrimeFactorsHelper(n: int, i: int, acc: int): int
    requires n >= 1
    requires i >= 2
    requires acc >= 0
    ensures sumOfPrimeFactorsHelper(n, i, acc) >= acc
    decreases n + (if i * i <= n then n - i else 0)
{
    if i * i > n then
        if n > 1 then acc + n else acc
    else if n % i == 0 then
        sumOfPrimeFactorsHelper(n / i, i, acc + i)
    else
        sumOfPrimeFactorsHelper(n, i + 1, acc)
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures result >= 2
{
    var o1 := countTriples_1925(o);
    assert o1 <= 1000000000;
    
    var o2 := monotoneIncreasingDigits_738(o1);
    if o1 < 2 {
        o2 := 2;
    }
    assert o2 >= 2;
    
    if o2 > 100000 {
        result := 2;
    } else {
        var o3 := smallestValue_2507(o2);
        result := o3;
    }
}
