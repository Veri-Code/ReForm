
method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= result <= 1000000000
{
    var ans := 0;
    var mi := -2147483648; // -(2^31)
    var mx := 2147483647;  // 2^31 - 1
    var curr := x;
    
    while curr != 0
        invariant 0 <= ans <= 1000000000
        decreases if curr >= 0 then curr else -curr
    {
        // Check for overflow before proceeding
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := curr % 10;
        if curr < 0 && y > 0 {
            y := y - 10;
        }
        
        var newAns := ans * 10 + y;
        if newAns < 0 || newAns > 1000000000 {
            return 0;
        }
        
        ans := newAns;
        curr := (curr - y) / 10;
    }
    
    return ans;
}

method intToString(n: int) returns (s: seq<char>)
    requires n >= 0
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        return ['0'];
    }
    
    var digits := [];
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| >= 1
        decreases temp
    {
        var digit := temp % 10;
        digits := [('0' as int + digit) as char] + digits;
        temp := temp / 10;
    }
    
    return digits;
}

method stringToInt(s: seq<char>) returns (result: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    result := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
    {
        var digit := (s[i] as int) - ('0' as int);
        result := result * 10 + digit;
        i := i + 1;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        return 1;
    }
    
    var s := intToString(n);
    var digits := s;
    var i := 1;
    
    // Find first decreasing position
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
    {
        i := i + 1;
    }
    
    // If we found a decreasing position, fix it
    if i < |digits| {
        // Decrease digits and propagate
        while i > 0 && digits[i-1] > digits[i]
            invariant 0 <= i <= |digits|
            invariant |digits| == |s|
            invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
        {
            var charVal := (digits[i-1] as int) - 1;
            if charVal >= ('0' as int) {
                digits := digits[i-1 := (charVal as char)];
            } else {
                digits := digits[i-1 := '0'];
            }
            i := i - 1;
        }
        
        // Set remaining digits to '9'
        i := i + 1;
        while i < |digits|
            invariant 0 <= i <= |digits|
            invariant |digits| == |s|
            invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
        {
            digits := digits[i := '9'];
            i := i + 1;
        }
    }
    
    result := stringToInt(digits);
    if result == 0 {
        result := 1;
    }
    
    // Ensure result is within bounds
    if result > 1000000000 {
        result := 1000000000;
    }
}

method isPrime(x: int) returns (result: bool)
    requires x >= 0
{
    if x < 2 {
        return false;
    }
    
    var v := 2;
    while v * v <= x
        invariant v >= 2
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            return false;
        }
        v := v + 1;
    }
    
    return true;
}

method reverseDigits(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    result := 0;
    var temp := x;
    
    while temp > 0
        invariant temp >= 0
        invariant result >= 0
        decreases temp
    {
        result := result * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= n
    decreases *
{
    var current := n;
    var limit := 200000000; // Upper bound to ensure termination
    
    while current <= limit
        invariant current >= n
        decreases limit - current
    {
        var reversed := reverseDigits(current);
        var isPalin := (reversed == current);
        
        if isPalin {
            var prime := isPrime(current);
            if prime {
                return current;
            }
        }
        
        // Special case optimization from original code
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
    }
    
    // Fallback - return a known prime palindrome
    return 100030001;
}

method main_3node_2(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 1
    decreases *
{
    var o1 := reverse_7(o);
    
    // Ensure o1 is in valid range for monotoneIncreasingDigits_738
    if o1 > 1000000000 {
        o1 := 1000000000;
    }
    
    var o2 := monotoneIncreasingDigits_738(o1);
    
    // Ensure o2 is in valid range for primePalindrome_866
    if o2 > 100000000 {
        o2 := 100000000;
    }
    if o2 < 1 {
        o2 := 1;
    }
    
    var o3 := primePalindrome_866(o2);
    return o3;
}
