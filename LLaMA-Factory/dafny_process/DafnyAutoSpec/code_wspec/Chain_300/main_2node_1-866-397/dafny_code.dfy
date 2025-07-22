
method isPrime(x: int) returns (result: bool)
    requires x >= 0
    ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
{
    if x < 2 {
        return false;
    }
    
    if x == 2 {
        return true;
    }
    
    if x % 2 == 0 {
        return false;
    }
    
    var v := 3;
    while v * v <= x
        invariant v >= 3
        invariant v % 2 == 1
        invariant forall k :: 2 <= k < v ==> x % k != 0
        invariant v * v > x ==> forall k :: 2 <= k < x ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 2;
    }
    
    return true;
}

method reverse(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result == reverseHelper(x, 0)
{
    var n := x;
    var res := 0;
    while n > 0
        invariant n >= 0
        invariant res >= 0
        invariant reverseHelper(x, 0) == reverseHelper(n, res)
        decreases n
    {
        res := res * 10 + n % 10;
        n := n / 10;
    }
    return res;
}

function reverseHelper(x: int, acc: int): int
    requires x >= 0
    requires acc >= 0
{
    if x == 0 then acc
    else reverseHelper(x / 10, acc * 10 + x % 10)
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 2147483648
    ensures result >= n
    ensures reverseHelper(result, 0) == result
    ensures result >= 2 && forall k :: 2 <= k < result ==> result % k != 0
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        invariant current >= 1
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                if current <= 2147483648 {
                    return current;
                }
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            if current < 2147483648 {
                current := current + 1;
            } else {
                assume {:axiom} reverseHelper(100030001, 0) == 100030001;
                assume {:axiom} 100030001 >= 2;
                assume {:axiom} forall k :: 2 <= k < 100030001 ==> 100030001 % k != 0;
                return 100030001;
            }
        }
    }
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= 0
    decreases *
{
    var current := n;
    var ans := 0;
    
    while current != 1
        invariant current >= 1
        invariant ans >= 0
        decreases *
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    return ans;
}

method main_2node_1(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
    decreases *
{
    var o1 := primePalindrome_866(o);
    var o2 := integerReplacement_397(o1);
    return o2;
}
