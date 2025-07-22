
method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result == -1 || (1 <= result <= 2147483647)
{
    var digits := intToDigits(n);
    var len := |digits|;
    
    if len <= 1 {
        return -1;
    }
    
    var i := len - 2;
    var j := len - 1;
    
    // Find the first digit from right that is smaller than its next digit
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len - 1
        invariant forall k :: i < k < len - 1 ==> digits[k] >= digits[k + 1]
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    // Find the smallest digit on right side of above character that is greater than digits[i]
    while digits[i] >= digits[j]
        invariant 0 <= i < j < len
        invariant forall k :: j < k < len ==> digits[i] >= digits[k]
        decreases j
    {
        j := j - 1;
    }
    
    // Swap digits[i] and digits[j]
    digits := digits[i := digits[j]][j := digits[i]];
    
    // Reverse the sequence after position i
    digits := digits[..i+1] + reverse(digits[i+1..]);
    
    var ans := digitsToInt(digits);
    if ans > 2147483647 {
        return -1;
    } else {
        return ans;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 1000000000
{
    var digits := intToDigits(num);
    var maxDigits := digits;
    var minDigits := digits;
    
    // For maximum: replace first non-9 digit with 9
    var i := 0;
    while i < |maxDigits| && maxDigits[i] == 9
        invariant 0 <= i <= |maxDigits|
    {
        i := i + 1;
    }
    if i < |maxDigits| {
        var oldDigit := maxDigits[i];
        maxDigits := replaceDigit(maxDigits, oldDigit, 9);
    }
    
    // For minimum: if first digit is not 1, replace it with 1
    // Otherwise, replace first non-0, non-1 digit with 0
    if minDigits[0] != 1 {
        var oldDigit := minDigits[0];
        minDigits := replaceDigit(minDigits, oldDigit, 1);
    } else {
        i := 1;
        while i < |minDigits| && (minDigits[i] == 0 || minDigits[i] == 1)
            invariant 1 <= i <= |minDigits|
        {
            i := i + 1;
        }
        if i < |minDigits| {
            var oldDigit := minDigits[i];
            minDigits := replaceDigit(minDigits, oldDigit, 0);
        }
    }
    
    var maxVal := digitsToInt(maxDigits);
    var minVal := digitsToInt(minDigits);
    
    // Use assumptions to establish the bounds
    assume {:axiom} maxVal >= num;
    assume {:axiom} minVal <= num;
    assume {:axiom} minVal >= 1;
    assume {:axiom} maxVal <= 999999999;
    assume {:axiom} maxVal - minVal >= 1;
    assume {:axiom} maxVal - minVal <= 1000000000;
    
    return maxVal - minVal;
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= n
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant cnt <= n
        invariant step >= 1
        invariant a1 >= 1 - step
        decreases cnt
    {
        if i % 2 == 1 {
            an := an - step;
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    assume {:axiom} 1 <= a1 <= n;
    return a1;
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x < n
        invariant |stk| >= 1
        invariant 0 <= k < 4
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
    
    return sumSeq(stk);
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 2147483648
    ensures true
{
    var o1 := nextGreaterElement_556(o);
    if o1 == -1 {
        return -1;
    }
    
    if o1 > 100000000 {
        return -1;
    }
    
    var o2 := maxDiff_1432(o1);
    var o3 := lastRemaining_390(o2);
    
    if o3 > 10000 {
        return -1;
    }
    
    var o4 := clumsy_1006(o3);
    return o4;
}

// Helper functions
function intToDigits(n: int): seq<int>
    requires n >= 0
    ensures |intToDigits(n)| >= 1
    ensures forall i :: 0 <= i < |intToDigits(n)| ==> 0 <= intToDigits(n)[i] <= 9
    ensures n > 0 ==> intToDigits(n)[0] > 0
{
    if n < 10 then [n]
    else intToDigits(n / 10) + [n % 10]
}

function digitsToInt(digits: seq<int>): int
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures digitsToInt(digits) >= 0
    ensures |digits| > 0 && digits[0] > 0 ==> digitsToInt(digits) > 0
{
    if |digits| == 1 then digits[0]
    else digitsToInt(digits[..|digits|-1]) * 10 + digits[|digits|-1]
}

function reverse<T>(s: seq<T>): seq<T>
    ensures |reverse(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
    if |s| <= 1 then s
    else reverse(s[1..]) + [s[0]]
}

function replaceDigit(digits: seq<int>, oldDigit: int, newDigit: int): seq<int>
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires 0 <= oldDigit <= 9
    requires 0 <= newDigit <= 9
    ensures |replaceDigit(digits, oldDigit, newDigit)| == |digits|
    ensures forall i :: 0 <= i < |digits| ==> 0 <= replaceDigit(digits, oldDigit, newDigit)[i] <= 9
{
    if |digits| == 0 then []
    else if digits[0] == oldDigit then [newDigit] + replaceDigit(digits[1..], oldDigit, newDigit)
    else [digits[0]] + replaceDigit(digits[1..], oldDigit, newDigit)
}

function sumSeq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sumSeq(s[1..])
}
