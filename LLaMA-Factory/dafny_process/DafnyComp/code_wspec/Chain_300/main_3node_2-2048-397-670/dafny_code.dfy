
method DigitCount(n: int) returns (counts: array<int>)
    requires n >= 0
    ensures counts.Length == 10
    ensures forall i :: 0 <= i < 10 ==> counts[i] >= 0
{
    counts := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
    {
        var digit := temp % 10;
        counts[digit] := counts[digit] + 1;
        temp := temp / 10;
    }
}

method IsBeautiful(n: int) returns (beautiful: bool)
    requires n >= 0
{
    var counts := DigitCount(n);
    beautiful := true;
    var i := 0;
    while i < 10 && beautiful
        invariant 0 <= i <= 10
    {
        if counts[i] != 0 && counts[i] != i {
            beautiful := false;
        }
        i := i + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 2147483648
{
    var x := n + 1;
    while x <= 2147483648
        invariant n + 1 <= x <= 2147483649
    {
        var isBeautiful := IsBeautiful(x);
        if isBeautiful {
            result := x;
            return;
        }
        x := x + 1;
    }
    result := 1;
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 0 <= result <= 100000000
{
    var current := n;
    var steps := 0;
    
    while current != 1 && steps < 100000000
        invariant current >= 1
        invariant steps >= 0
        invariant steps <= 100000000
        decreases if current == 1 then 0 else 100000000 - steps
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        steps := steps + 1;
    }
    
    result := steps;
}

method IntToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
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
        invariant temp > 0 ==> |result| >= 0
        invariant temp == 0 ==> |result| >= 1
    {
        var digit := temp % 10;
        result := [digit] + result;
        temp := temp / 10;
    }
    
    digits := result;
}

method DigitsToInt(digits: seq<int>) returns (num: int)
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
    requires 0 <= num <= 100000000
    ensures result >= 0
    ensures result <= 100000000
{
    var digits := IntToDigits(num);
    var n := |digits|;
    
    if n <= 1 {
        result := num;
        return;
    }
    
    var maxRight := new int[n];
    maxRight[n-1] := n-1;
    
    var i := n - 2;
    while i >= 0
        invariant -1 <= i < n
        invariant forall j :: i + 1 <= j < n ==> 0 <= maxRight[j] < n
    {
        if digits[i] <= digits[maxRight[i+1]] {
            maxRight[i] := maxRight[i+1];
        } else {
            maxRight[i] := i;
        }
        i := i - 1;
    }
    
    var swapped := false;
    var resultDigits := digits;
    i := 0;
    while i < n && !swapped
        invariant 0 <= i <= n
        invariant |resultDigits| == |digits|
        invariant forall k :: 0 <= k < |resultDigits| ==> 0 <= resultDigits[k] <= 9
    {
        var j := maxRight[i];
        if j < |digits| && digits[i] < digits[j] {
            resultDigits := resultDigits[i := digits[j]][j := digits[i]];
            swapped := true;
        }
        i := i + 1;
    }
    
    var temp := DigitsToInt(resultDigits);
    if temp <= 100000000 {
        result := temp;
    } else {
        result := num;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures 0 <= result <= 100000000
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2 := integerReplacement_397(o1);
    var o3 := maximumSwap_670(o2);
    result := o3;
}
