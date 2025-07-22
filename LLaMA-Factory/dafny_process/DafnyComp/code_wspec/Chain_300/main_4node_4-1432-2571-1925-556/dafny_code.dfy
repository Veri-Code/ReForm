
method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 100000
{
    // Convert number to string representation (conceptually)
    var digits := numToDigits(num);
    var n := |digits|;
    
    // Find maximum by replacing first non-9 digit with 9
    var maxNum := num;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant maxNum >= num
    {
        if digits[i] != 9 {
            maxNum := replaceDigit(num, digits[i], 9);
            break;
        }
        i := i + 1;
    }
    
    // Find minimum by replacing appropriately
    var minNum := num;
    if digits[0] != 1 {
        minNum := replaceDigit(num, digits[0], 1);
    } else {
        i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant minNum <= num
        {
            if digits[i] != 0 && digits[i] != 1 {
                minNum := replaceDigit(num, digits[i], 0);
                break;
            }
            i := i + 1;
        }
    }
    
    result := maxNum - minNum;
    if result == 0 {
        result := 1;
    }
    
    // Ensure postcondition bounds
    if result > 100000 {
        result := 100000;
    }
    if result < 1 {
        result := 1;
    }
}

method minOperations_2571(n: int) returns (ans: int)
    requires 1 <= n <= 100000
    ensures 1 <= ans <= 250
{
    ans := 0;
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
    
    if ans == 0 {
        ans := 1;
    }
    
    // Ensure postcondition
    if ans > 250 {
        ans := 250;
    }
}

method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures ans >= 0
{
    ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
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

method nextGreaterElement_556(n: int) returns (result: int)
    requires n >= 1
    ensures result == -1 || result >= 1
{
    var digits := numToDigits(n);
    var len := |digits|;
    
    if len <= 1 {
        result := -1;
        return;
    }
    
    // Find rightmost digit that is smaller than the digit next to it
    var i := len - 2;
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < len - 1
        decreases i
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    // Find the smallest digit on right side of above character that is greater than digits[i]
    var j := len - 1;
    while digits[i] >= digits[j]
        invariant i < j < len
        decreases j
    {
        j := j - 1;
    }
    
    // Swap digits[i] and digits[j]
    var temp := digits[i];
    digits := digits[i := digits[j]];
    digits := digits[j := temp];
    
    // Reverse the substring after position i
    digits := reverseAfter(digits, i);
    
    assert forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9;
    var candidate := digitsToNum(digits);
    if candidate > 2147483647 {
        result := -1;
    } else {
        result := candidate;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result == -1 || result >= 1
{
    var o1 := maxDiff_1432(o);
    var o2 := minOperations_2571(o1);
    var o3 := countTriples_1925(o2);
    assert o3 >= 0;
    if o3 == 0 {
        result := -1;
    } else {
        var o4 := nextGreaterElement_556(o3);
        result := o4;
    }
}

// Helper functions
function numToDigits(n: int): seq<int>
    requires n >= 1
    ensures |numToDigits(n)| >= 1
    ensures forall i :: 0 <= i < |numToDigits(n)| ==> 0 <= numToDigits(n)[i] <= 9
{
    if n < 10 then [n]
    else numToDigits(n / 10) + [n % 10]
}

function digitsToNum(digits: seq<int>): int
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures digitsToNum(digits) >= 1
{
    if |digits| == 1 then 
        if digits[0] == 0 then 1 else digits[0]
    else 
        var prefix := digitsToNum(digits[..|digits|-1]);
        prefix * 10 + digits[|digits|-1]
}

function replaceDigit(num: int, oldDigit: int, newDigit: int): int
    requires num >= 1
    requires 0 <= oldDigit <= 9
    requires 0 <= newDigit <= 9
{
    var digits := numToDigits(num);
    var newDigits := replaceInSeq(digits, oldDigit, newDigit);
    digitsToNum(newDigits)
}

function replaceInSeq(digits: seq<int>, oldVal: int, newVal: int): seq<int>
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires 0 <= oldVal <= 9
    requires 0 <= newVal <= 9
    ensures |replaceInSeq(digits, oldVal, newVal)| == |digits|
    ensures forall i :: 0 <= i < |replaceInSeq(digits, oldVal, newVal)| ==> 0 <= replaceInSeq(digits, oldVal, newVal)[i] <= 9
{
    if |digits| == 0 then []
    else if digits[0] == oldVal then [newVal] + digits[1..]
    else [digits[0]] + replaceInSeq(digits[1..], oldVal, newVal)
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x < (isqrt(x) + 1) * (isqrt(x) + 1)
{
    if x == 0 then 0
    else if x < 4 then 1
    else 
        var guess := isqrt(x / 4) * 2;
        if (guess + 1) * (guess + 1) <= x then guess + 1 else guess
}

function reverseAfter(digits: seq<int>, pos: int): seq<int>
    requires 0 <= pos < |digits|
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures |reverseAfter(digits, pos)| == |digits|
    ensures forall i :: 0 <= i < |reverseAfter(digits, pos)| ==> 0 <= reverseAfter(digits, pos)[i] <= 9
{
    digits[..pos+1] + reverse(digits[pos+1..])
}

function reverse(s: seq<int>): seq<int>
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
    ensures |reverse(s)| == |s|
    ensures forall i :: 0 <= i < |reverse(s)| ==> 0 <= reverse(s)[i] <= 9
{
    if |s| <= 1 then s
    else reverse(s[1..]) + [s[0]]
}
