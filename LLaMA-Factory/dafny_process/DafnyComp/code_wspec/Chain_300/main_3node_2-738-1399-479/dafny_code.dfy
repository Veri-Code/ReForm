
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method intToString(n: int) returns (s: seq<char>)
    requires n >= 0
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        s := ['0'];
        return;
    }
    
    var temp := n;
    var digits: seq<char> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| >= 1
    {
        var digit := temp % 10;
        var digitChar := (digit as char) + '0';
        digits := [digitChar] + digits;
        temp := temp / 10;
    }
    
    s := digits;
}

method stringToInt(s: seq<char>) returns (n: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures n >= 0
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
    {
        var digitValue := (s[i] as int) - ('0' as int);
        n := n * 10 + digitValue;
        i := i + 1;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 10000
{
    var s := intToString(n);
    var digits := s;
    var i := 1;
    
    // Find first decreasing position
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
        invariant forall j :: 1 <= j < i ==> digits[j-1] <= digits[j]
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Fix decreasing digits
        while i > 0 && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            invariant |digits| == |s|
            invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
        {
            var prevDigitValue := (digits[i-1] as int) - ('0' as int);
            if prevDigitValue > 0 {
                digits := digits[i-1 := (prevDigitValue - 1) as char + '0'];
            }
            i := i - 1;
        }
        
        i := i + 1;
        // Set remaining digits to 9
        while i < |digits|
            invariant 0 <= i <= |digits|
            invariant |digits| == |s|
            invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
        {
            digits := digits[i := '9'];
            i := i + 1;
        }
    }
    
    var temp_result := stringToInt(digits);
    if temp_result <= 10000 && temp_result >= 1 {
        result := temp_result;
    } else if temp_result > 10000 {
        result := 10000;
    } else {
        result := 1;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 8
{
    // Use arrays to simulate Counter
    var maxSum := 36; // max possible digit sum for numbers up to 10000 (9999 -> 36)
    var counts := new int[maxSum + 1];
    var i := 0;
    while i <= maxSum
        invariant 0 <= i <= maxSum + 1
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var num := 1;
    while num <= n
        invariant 1 <= num <= n + 1
        invariant forall j :: 0 <= j <= maxSum ==> counts[j] >= 0
    {
        var sum := digitSum(num);
        if sum <= maxSum {
            counts[sum] := counts[sum] + 1;
        }
        num := num + 1;
    }
    
    // Find maximum count
    var maxCount := 0;
    i := 0;
    while i <= maxSum
        invariant 0 <= i <= maxSum + 1
        invariant maxCount >= 0
    {
        if counts[i] > maxCount {
            maxCount := counts[i];
        }
        i := i + 1;
    }
    
    // Count how many groups have the maximum count
    var answer := 0;
    i := 0;
    while i <= maxSum
        invariant 0 <= i <= maxSum + 1
        invariant answer >= 0
    {
        if counts[i] == maxCount {
            answer := answer + 1;
        }
        i := i + 1;
    }
    
    if answer == 0 || answer > 8 {
        result := 1;
    } else {
        result := answer;
    }
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) > 0
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}

method reverseNumber(a: int) returns (result: int)
    requires a >= 0
    ensures result >= 0
{
    var b := a;
    var x := a;
    while b > 0
        invariant b >= 0
        invariant x >= 0
    {
        x := x * 10 + (b % 10);
        b := b / 10;
    }
    result := x;
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 0 <= result
{
    if n == 1 {
        result := 9;
        return;
    }
    
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx > 0
        decreases a
    {
        var x := reverseNumber(a);
        var t := mx;
        
        while t * t >= x && t > 0
            invariant t >= 0
            invariant x >= 0
        {
            if x % t == 0 {
                result := x % 1337;
                return;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    result := 9;
}

method main_3node_2(o: int) returns (result: int)
    requires 0 <= o <= 1000000000
    ensures 0 <= result
{
    var o1 := monotoneIncreasingDigits_738(o);
    var o2 := countLargestGroup_1399(o1);
    var o3 := largestPalindrome_479(o2);
    result := o3;
}
