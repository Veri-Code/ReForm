
method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
    ensures result <= n || n == 0
{
    if n == 0 {
        return 1;
    }
    
    var digits := intToDigits(n);
    var len := |digits|;
    
    var i := 1;
    while i < len && digits[i-1] <= digits[i]
        invariant 1 <= i <= len
        invariant forall k :: 0 <= k < i-1 ==> digits[k] <= digits[k+1]
    {
        i := i + 1;
    }
    
    if i < len {
        while i > 0 && digits[i-1] > digits[i]
            invariant 0 <= i < len
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
            invariant |digits| == len
            decreases i
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        while i < len
            invariant i <= len
            invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
            invariant |digits| == len
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(digits);
    if result == 0 {
        result := 1;
    }
    
    // Ensure postconditions
    if result > n {
        result := n;
    }
    if result < 1 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 0
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases num
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483647
    ensures -2147483648 <= result <= 2147483647
{
    var ans := 0;
    var mi := -214748364;
    var mx := 214748364;
    var num := x;
    
    while num != 0
        invariant -2147483648 <= ans <= 2147483647
        decreases if num >= 0 then num else -num
    {
        if ans < mi || ans > mx {
            return 0;
        }
        
        var y := num % 10;
        if num < 0 && y > 0 {
            y := y - 10;
        }
        
        // Check for overflow before multiplication
        if ans > 0 && ans > 214748364 {
            return 0;
        }
        if ans < 0 && ans < -214748364 {
            return 0;
        }
        if ans == 214748364 && y > 7 {
            return 0;
        }
        if ans == -214748364 && y < -8 {
            return 0;
        }
        
        ans := ans * 10 + y;
        num := (num - y) / 10;
    }
    
    result := ans;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 1000000000
    ensures result >= 2
    ensures result <= 1000000000
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
        
        while i * i <= temp
            invariant i >= 2
            invariant s >= 0
            invariant temp >= 1
            invariant current >= 2
        {
            while temp % i == 0
                invariant temp >= 1
                invariant i >= 2
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
            return t;
        }
        current := s;
        if current < 2 {
            current := 2;
        }
        if current > 1000000000 {
            return 1000000000;
        }
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= n
    ensures result <= 1000000000
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant k >= 0
        invariant a >= 0
        invariant b >= 0
        decreases t
    {
        if t % 10 % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
        var res := x + y;
        if res > 1000000000 || res < n {
            return 1000000000;
        }
        return res;
    }
    
    if a == b {
        return n;
    }
    
    if n < 1000000000 {
        var nextResult := closestFair_2417(n + 1);
        return nextResult;
    } else {
        return n;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures result >= 0
    decreases *
{
    var o1 := monotoneIncreasingDigits_738(o);
    
    var o2 := minOperations_2571(o1);
    
    // Handle case where o2 might be outside reverse_7's range
    if o2 > 2147483647 {
        result := 2;
        return;
    }
    
    var o3 := reverse_7(o2);
    if o3 < 2 {
        result := 2;
        return;
    }
    
    // Handle case where o3 might be outside smallestValue_2507's range
    if o3 > 1000000000 {
        result := o3;
        return;
    }
    
    var o4 := smallestValue_2507(o3);
    
    // Handle case where o4 might be outside closestFair_2417's range
    if o4 > 1000000000 {
        result := o4;
        return;
    }
    
    var o5 := closestFair_2417(o4);
    result := o5;
}

// Helper functions
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

function power10(n: int): int
    requires n >= 0
    ensures power10(n) >= 1
    ensures n > 0 ==> power10(n) >= 10
    ensures n >= 1 ==> power10(n) >= power10(n-1)
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}
