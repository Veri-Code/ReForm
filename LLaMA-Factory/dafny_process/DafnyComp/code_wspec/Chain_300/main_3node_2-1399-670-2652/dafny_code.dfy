
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
    ensures 1 <= result <= 100000000
{
    // Map digit sums to their counts
    var counts := map[];
    var maxCount := 1;
    var groupsWithMaxCount := 1;
    
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 1
        invariant groupsWithMaxCount >= 1
        invariant groupsWithMaxCount <= i
    {
        var ds := digitSum(i);
        
        var currentCount := if ds in counts then counts[ds] else 0;
        currentCount := currentCount + 1;
        counts := counts[ds := currentCount];
        
        if maxCount < currentCount {
            maxCount := currentCount;
            groupsWithMaxCount := 1;
        } else if maxCount == currentCount {
            groupsWithMaxCount := groupsWithMaxCount + 1;
        }
        
        i := i + 1;
    }
    
    result := groupsWithMaxCount;
}

method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if num == 0 {
        digits := [0];
        return;
    }
    
    var temp := num;
    digits := [];
    
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp == 0 ==> |digits| >= 1
    {
        var digit := temp % 10;
        digits := [digit] + digits;
        temp := temp / 10;
    }
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
    requires 0 <= num <= 100000000
    ensures 1 <= result <= 1000
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    if n <= 1 {
        result := if num == 0 then 1 else if num <= 1000 then num else 1000;
        return;
    }
    
    // Find the rightmost position of the largest digit for each position
    var maxIndices := new int[n];
    maxIndices[n-1] := n-1;
    
    var i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant forall j :: i + 1 <= j < n ==> 0 <= maxIndices[j] < n
    {
        if digits[i] <= digits[maxIndices[i + 1]] {
            maxIndices[i] := maxIndices[i + 1];
        } else {
            maxIndices[i] := i;
        }
        i := i - 1;
    }
    
    // Find the first position where we can make a beneficial swap
    var swapped := false;
    i := 0;
    while i < n && !swapped
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < n ==> 0 <= maxIndices[j] < n
        invariant |digits| == n
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        var j := maxIndices[i];
        if digits[i] < digits[j] {
            // Perform the swap
            var temp := digits[i];
            digits := digits[i := digits[j]];
            digits := digits[j := temp];
            swapped := true;
        }
        i := i + 1;
    }
    
    var resultValue := digitsToInt(digits);
    result := if resultValue >= 1 && resultValue <= 1000 then resultValue else if resultValue > 1000 then 1000 else 1;
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 1
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
    
    if result == 0 {
        result := 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures 1 <= result
{
    var o1 := countLargestGroup_1399(o);
    var o2 := maximumSwap_670(o1);
    var o3 := sumOfMultiples_2652(o2);
    result := o3;
}
