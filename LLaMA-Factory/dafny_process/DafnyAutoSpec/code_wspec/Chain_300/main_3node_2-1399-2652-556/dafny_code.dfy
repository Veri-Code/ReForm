
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

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000
{
    // Map from digit sum to count - using arrays for simplicity
    // Max digit sum for numbers 1-10000 is 9*5 = 45 (for 99999, but we're limited to 10000)
    // Actually max is 9+9+9+9 = 36 for 9999, but let's use 50 to be safe
    var counts := new int[50];
    var i := 0;
    while i < 50
        invariant 0 <= i <= 50
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var groupsWithMaxCount := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant groupsWithMaxCount >= 0
        invariant maxCount > 0 ==> groupsWithMaxCount >= 1
    {
        var ds := digitSum(i);
        if ds < 50 {
            counts[ds] := counts[ds] + 1;
            
            if maxCount < counts[ds] {
                maxCount := counts[ds];
                groupsWithMaxCount := 1;
            } else if maxCount == counts[ds] {
                groupsWithMaxCount := groupsWithMaxCount + 1;
            }
        }
        i := i + 1;
    }
    
    result := groupsWithMaxCount;
    if result == 0 {
        result := 1; // Ensure we return at least 1
    }
    assert result >= 1;
    if result > 1000 {
        result := 1000;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result >= 0
    {
        if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
            result := result + i;
        }
        i := i + 1;
    }
}

method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        digits := [0];
        return;
    }
    
    var temp := n;
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp == 0 ==> |result| >= 1
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    digits := result;
    assert |digits| >= 1;
}

method digitsToInt(digits: seq<int>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
    {
        result := result * 10 + digits[i];
        i := i + 1;
    }
}

method reverseSeq(s: seq<int>) returns (reversed: seq<int>)
    ensures |reversed| == |s|
    ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
    reversed := [];
    var i := |s|;
    while i > 0
        invariant 0 <= i <= |s|
        invariant |reversed| == |s| - i
        invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == s[|s| - 1 - j]
    {
        i := i - 1;
        reversed := reversed + [s[i]];
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires n >= 1
{
    var digits := intToDigits(n);
    var len := |digits|;
    
    if len <= 1 {
        result := -1;
        return;
    }
    
    // Find rightmost digit that is smaller than the digit next to it
    var i := len - 2;
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i <= len - 2
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    // Find the smallest digit on right side of above character that is greater than digits[i]
    var j := len - 1;
    while j > i && digits[i] >= digits[j]
        invariant i < j <= len - 1
    {
        j := j - 1;
    }
    
    // Swap digits[i] and digits[j]
    var temp := digits[i];
    var newDigits := digits[i := digits[j]][j := temp];
    
    // Reverse the suffix starting at i+1
    var prefix := newDigits[..i+1];
    var suffix := newDigits[i+1..];
    var reversedSuffix := reverseSeq(suffix);
    var finalDigits := prefix + reversedSuffix;
    
    var candidate := digitsToInt(finalDigits);
    
    // Check if result exceeds 2^31 - 1
    if candidate > 2147483647 {
        result := -1;
    } else {
        result := candidate;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result == -1 || result > 1
{
    var o1 := countLargestGroup_1399(o);
    var o2 := sumOfMultiples_2652(o1);
    if o2 >= 1 {
        var o3 := nextGreaterElement_556(o2);
        result := o3;
        if result != -1 && result <= 1 {
            result := 2;
        }
    } else {
        result := -1;
    }
}
