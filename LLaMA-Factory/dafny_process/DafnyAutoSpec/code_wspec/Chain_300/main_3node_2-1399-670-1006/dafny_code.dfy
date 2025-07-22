
method digitSum(num: int) returns (sum: int)
    requires num >= 0
    ensures sum >= 0
{
    var n := num;
    sum := 0;
    while n > 0
        invariant sum >= 0
        invariant n >= 0
    {
        sum := sum + (n % 10);
        n := n / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result
{
    // We'll use arrays to simulate the counter
    // Maximum possible digit sum for numbers 1..10000 is 9*4 = 36
    var counts := new int[37];
    var i := 0;
    while i < 37
        invariant 0 <= i <= 37
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var answer := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant answer >= 0
        invariant forall j :: 0 <= j < 37 ==> counts[j] >= 0
    {
        var ds := digitSum(i);
        if ds < 37 {
            counts[ds] := counts[ds] + 1;
            if maxCount < counts[ds] {
                maxCount := counts[ds];
                answer := 1;
            } else if maxCount == counts[ds] {
                answer := answer + 1;
            }
        }
        i := i + 1;
    }
    
    if answer == 0 {
        result := 1;
    } else {
        result := answer;
    }
}

method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures num == 0 ==> digits == [0]
{
    if num == 0 {
        digits := [0];
        return;
    }
    
    var temp := num;
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp == 0 ==> |result| >= 1
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    digits := result;
}

method digitsToInt(digits: seq<int>) returns (num: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures num >= 0
{
    num := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant num >= 0
    {
        num := num * 10 + digits[i];
        i := i + 1;
    }
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num
    ensures result >= 0
    ensures result >= 1
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    if n <= 1 {
        result := if num == 0 then 1 else num;
        return;
    }
    
    // Find the rightmost position of maximum digit for each position
    var maxIdx := new int[n];
    maxIdx[n-1] := n-1;
    
    var i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant forall j :: i + 1 <= j < n ==> 0 <= maxIdx[j] < n
    {
        if digits[i] <= digits[maxIdx[i + 1]] {
            maxIdx[i] := maxIdx[i + 1];
        } else {
            maxIdx[i] := i;
        }
        i := i - 1;
    }
    
    // Find first position where we can make a beneficial swap
    var swapped := false;
    var newDigits := digits;
    i := 0;
    while i < n && !swapped
        invariant 0 <= i <= n
        invariant |newDigits| == |digits|
        invariant forall j :: 0 <= j < |newDigits| ==> 0 <= newDigits[j] <= 9
        invariant !swapped ==> newDigits == digits
    {
        var j := maxIdx[i];
        if digits[i] < digits[j] {
            newDigits := newDigits[i := digits[j]][j := digits[i]];
            swapped := true;
        }
        i := i + 1;
    }
    
    var temp := digitsToInt(newDigits);
    result := if temp == 0 then 1 else temp;
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n
{
    var stack: seq<int> := [n];
    var k := 0;
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stack| >= 1
    {
        if k == 0 {
            // Multiplication
            var top := stack[|stack| - 1];
            stack := stack[..|stack| - 1] + [top * x];
        } else if k == 1 {
            // Division
            var top := stack[|stack| - 1];
            var quotient := if top >= 0 then top / x else -((-top) / x);
            stack := stack[..|stack| - 1] + [quotient];
        } else if k == 2 {
            // Addition (push positive)
            stack := stack + [x];
        } else {
            // Subtraction (push negative)
            stack := stack + [-x];
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum all elements in stack
    result := 0;
    var i := 0;
    while i < |stack|
        invariant 0 <= i <= |stack|
    {
        result := result + stack[i];
        i := i + 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures true
{
    var o1 := countLargestGroup_1399(o);
    var o2 := maximumSwap_670(o1);
    var o3 := clumsy_1006(o2);
    result := o3;
}
