
method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= ans
{
    ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var curr_x := x;
    
    while curr_x != 0
        invariant ans >= 0
        decreases if curr_x >= 0 then curr_x else -curr_x
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := curr_x % 10;
        if curr_x < 0 && y > 0 {
            y := y - 10;
        }
        
        ans := ans * 10 + y;
        curr_x := (curr_x - y) / 10;
        
        if ans < 0 {
            return 0;
        }
    }
}

method is_prime(x: int) returns (result: bool)
    requires x >= 0
    ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
{
    if x < 2 {
        return false;
    }
    
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    
    // Need to prove that no divisors exist from v to x-1
    assert forall k :: 2 <= k < v ==> x % k != 0;
    assert v * v > x;
    
    // For any k where v <= k < x, if k divides x, then x/k < v
    // But x/k >= 2 (since k < x and k >= v >= 2), so x/k would be a divisor < v
    // This contradicts our invariant
    assert forall k :: v <= k < x ==> x % k != 0 by {
        forall k | v <= k < x
            ensures x % k != 0
        {
            if x % k == 0 {
                var quotient := x / k;
                assert quotient >= 2;
                assert quotient < v;
                assert x % quotient == 0;
                assert false;
            }
        }
    }
    
    return true;
}

method reverse(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    res := 0;
    var curr_x := x;
    
    while curr_x > 0
        invariant curr_x >= 0
        invariant res >= 0
        decreases curr_x
    {
        res := res * 10 + curr_x % 10;
        curr_x := curr_x / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= n
    ensures result <= 100000000
{
    var curr_n := n;
    
    while true
        invariant curr_n >= n
        decreases 100000000 - curr_n + 1
    {
        var rev := reverse(curr_n);
        if rev == curr_n {
            var prime := is_prime(curr_n);
            if prime {
                return curr_n;
            }
        }
        
        if 10000000 < curr_n < 100000000 {
            curr_n := 100000000;
        } else {
            curr_n := curr_n + 1;
        }
        
        if curr_n > 100000000 {
            return 100000000;
        }
    }
}

method minOperations_2571(n: int) returns (ans: int)
    requires 1 <= n <= 100000
    ensures ans >= 0
{
    ans := 0;
    var cnt := 0;
    var curr_n := n;
    
    while curr_n > 0
        invariant curr_n >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases curr_n
    {
        if curr_n % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        curr_n := curr_n / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
}

method count_digits(x: int) returns (digits: array<int>)
    requires x >= 0
    ensures digits.Length == 10
    ensures forall i :: 0 <= i < 10 ==> digits[i] >= 0
{
    digits := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> digits[j] == 0
    {
        digits[i] := 0;
        i := i + 1;
    }
    
    var curr_x := x;
    while curr_x > 0
        invariant curr_x >= 0
        invariant forall j :: 0 <= j < 10 ==> digits[j] >= 0
        decreases curr_x
    {
        var digit := curr_x % 10;
        digits[digit] := digits[digit] + 1;
        curr_x := curr_x / 10;
    }
}

method is_beautiful(x: int) returns (result: bool)
    requires x >= 0
{
    var cnt := count_digits(x);
    result := true;
    
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
    {
        if cnt[i] != 0 && i != cnt[i] {
            result := false;
            return;
        }
        i := i + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result > n
{
    var x := n + 1;
    
    while x <= 10000000
        invariant x > n
        decreases 10000000 - x + 1
    {
        var beautiful := is_beautiful(x);
        if beautiful {
            return x;
        }
        x := x + 1;
    }
    
    return 10000000;
}

method main_4node_4(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 1
{
    var o1 := reverse_7(o);
    if o1 == 0 || o1 > 100000000 {
        result := 1;
        return;
    }
    
    var o2 := primePalindrome_866(o1);
    if o2 > 100000 {
        result := 1;
        return;
    }
    
    var o3 := minOperations_2571(o2);
    if o3 > 1000000 {
        result := 1;
        return;
    }
    
    var o4 := nextBeautifulNumber_2048(o3);
    result := o4;
}
