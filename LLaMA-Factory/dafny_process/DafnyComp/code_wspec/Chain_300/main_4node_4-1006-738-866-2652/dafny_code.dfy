
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 1000000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        invariant forall i :: 0 <= i < |stk| ==> stk[i] >= -1000000000 && stk[i] <= 1000000000
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var new_val := top * x;
            if new_val > 1000000000 { new_val := 1000000000; }
            if new_val < -1000000000 { new_val := -1000000000; }
            stk := stk[..|stk| - 1] + [new_val];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            var new_val := top / x;
            stk := stk[..|stk| - 1] + [new_val];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant result >= -1000000000 && result <= 1000000000
        decreases |stk| - i
    {
        var new_result := result + stk[i];
        if new_result > 1000000000 { new_result := 1000000000; }
        if new_result < -1000000000 { new_result := -1000000000; }
        result := new_result;
        i := i + 1;
    }
    
    if result < 0 { result := 0; }
    if result > 1000000000 { result := 1000000000; }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        result := 1;
        return;
    }
    
    var digits := [];
    var temp := n;
    
    // Convert number to digits
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        result := 1;
        return;
    }
    
    var i := 1;
    while i < |digits| && digits[i - 1] <= digits[i]
        invariant 1 <= i <= |digits|
        decreases |digits| - i
    {
        i := i + 1;
    }
    
    if i < |digits| {
        while i > 0 && i < |digits| && digits[i - 1] > digits[i]
            invariant 0 <= i <= |digits|
            invariant |digits| > 0
            decreases i
        {
            if digits[i - 1] > 0 {
                digits := digits[i - 1 := digits[i - 1] - 1];
            }
            i := i - 1;
        }
        if i < |digits| {
            i := i + 1;
            while i < |digits|
                invariant i <= |digits|
                decreases |digits| - i
            {
                digits := digits[i := 9];
                i := i + 1;
            }
        }
    }
    
    // Convert digits back to number
    result := 0;
    i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
        invariant result <= 1000000000
        decreases |digits| - i
    {
        var new_result := result * 10 + digits[i];
        if new_result > 1000000000 { new_result := 1000000000; }
        if new_result < 0 { new_result := 0; }
        result := new_result;
        i := i + 1;
    }
    
    if result == 0 {
        result := 1;
    }
}

method is_prime(x: int) returns (prime: bool)
    requires x >= 0
{
    if x < 2 {
        prime := false;
        return;
    }
    
    var v := 2;
    prime := true;
    
    while v * v <= x && prime
        invariant 2 <= v
        invariant prime ==> (forall k :: 2 <= k < v ==> x % k != 0)
        decreases x - v * v + 1
    {
        if x % v == 0 {
            prime := false;
        }
        v := v + 1;
    }
}

method reverse(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    res := 0;
    var temp := x;
    
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
        decreases temp
    {
        res := res * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    var current := n;
    
    while current <= 1000000000
        invariant current >= n
        decreases 1000000000 - current
    {
        var rev := reverse(current);
        if rev == current {
            var is_prime_result := is_prime(current);
            if is_prime_result {
                result := current;
                return;
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    
    // Fallback
    result := 2;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 0
{
    result := 0;
    var x := 1;
    
    while x <= n && x <= 1000000
        invariant 1 <= x <= n + 1
        invariant result >= 0
        decreases 1000000 - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := clumsy_1006(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    var o3 := primePalindrome_866(o2);
    var o4 := sumOfMultiples_2652(o3);
    result := o4;
}
