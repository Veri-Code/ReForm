
method DigitSum(num: int) returns (sum: int)
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

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= num
    ensures result <= 999999999
{
    result := num;
    
    if num == 0 {
        return;
    }
    
    // Convert to sequence of digits
    var digits: seq<int> := [];
    var temp := num;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        return;
    }
    
    // Find the best swap
    var n := |digits|;
    var bestResult := num;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant bestResult >= num
        invariant bestResult <= 999999999
    {
        var j := i + 1;
        while j < n
            invariant i < j <= n
            invariant bestResult >= num
            invariant bestResult <= 999999999
        {
            if digits[j] > digits[i] {
                bestResult := num + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := bestResult;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result
{
    var counts: map<int, int> := map[];
    var maxCount := 0;
    
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant forall k :: k in counts ==> counts[k] >= 1
        invariant forall k :: k in counts ==> counts[k] <= maxCount
        invariant maxCount <= i - 1
    {
        var digitSum := DigitSum(i);
        
        if digitSum in counts {
            counts := counts[digitSum := counts[digitSum] + 1];
        } else {
            counts := counts[digitSum := 1];
        }
        
        if counts[digitSum] > maxCount {
            maxCount := counts[digitSum];
        }
        
        i := i + 1;
    }
    
    result := 0;
    var keys := set k | k in counts;
    
    while keys != {}
        invariant result >= 0
        invariant forall k :: k in counts ==> counts[k] <= maxCount
    {
        var k :| k in keys;
        keys := keys - {k};
        
        if k in counts && counts[k] == maxCount {
            result := result + 1;
        }
    }
    
    if result == 0 {
        result := 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
{
    var digits: seq<int> := [];
    var temp := num;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        result := 0;
        return;
    }
    
    var maxVal := num;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant maxVal >= num
        invariant forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
    {
        if digits[i] != 9 {
            var newDigits := digits;
            var j := 0;
            while j < |newDigits|
                invariant 0 <= j <= |newDigits|
                invariant |newDigits| == |digits|
                invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
            {
                if newDigits[j] == digits[i] {
                    newDigits := newDigits[j := 9];
                }
                j := j + 1;
            }
            
            var newNum := 0;
            var k := 0;
            while k < |newDigits|
                invariant 0 <= k <= |newDigits|
                invariant newNum >= 0
                invariant newNum <= 999999999
                invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
            {
                if newNum <= 99999999 {
                    newNum := newNum * 10 + newDigits[k];
                }
                k := k + 1;
            }
            maxVal := newNum;
            break;
        }
        i := i + 1;
    }
    
    var minVal := num;
    if |digits| > 0 {
        if digits[0] != 1 {
            var newDigits := digits;
            var replaceDigit := digits[0];
            var j := 0;
            while j < |newDigits|
                invariant 0 <= j <= |newDigits|
                invariant |newDigits| == |digits|
                invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
            {
                if newDigits[j] == replaceDigit {
                    newDigits := newDigits[j := 1];
                }
                j := j + 1;
            }
            
            var newNum := 0;
            var k := 0;
            while k < |newDigits|
                invariant 0 <= k <= |newDigits|
                invariant newNum >= 0
                invariant newNum <= 999999999
                invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
            {
                if newNum <= 99999999 {
                    newNum := newNum * 10 + newDigits[k];
                }
                k := k + 1;
            }
            minVal := newNum;
        } else {
            var i := 1;
            while i < |digits|
                invariant 1 <= i <= |digits|
                invariant forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
            {
                if digits[i] != 0 && digits[i] != 1 {
                    var newDigits := digits;
                    var replaceDigit := digits[i];
                    var j := 0;
                    while j < |newDigits|
                        invariant 0 <= j <= |newDigits|
                        invariant |newDigits| == |digits|
                        invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
                    {
                        if newDigits[j] == replaceDigit {
                            newDigits := newDigits[j := 0];
                        }
                        j := j + 1;
                    }
                    
                    var newNum := 0;
                    var k := 0;
                    while k < |newDigits|
                        invariant 0 <= k <= |newDigits|
                        invariant newNum >= 0
                        invariant newNum <= 999999999
                        invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
                    {
                        if newNum <= 99999999 {
                            newNum := newNum * 10 + newDigits[k];
                        }
                        k := k + 1;
                    }
                    minVal := newNum;
                    break;
                }
                i := i + 1;
            }
        }
    }
    
    if maxVal >= minVal {
        result := maxVal - minVal;
    } else {
        result := 0;
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires n >= 1
    ensures result == -1 || result > n
{
    var digits: seq<int> := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| <= 1 {
        result := -1;
        return;
    }
    
    var i := |digits| - 2;
    while i >= 0 && digits[i] >= digits[i + 1]
        invariant -1 <= i < |digits| - 1
        invariant forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    var j := |digits| - 1;
    while j > i && digits[i] >= digits[j]
        invariant i < j < |digits|
        invariant forall idx :: 0 <= idx < |digits| ==> 0 <= digits[idx] <= 9
    {
        j := j - 1;
    }
    
    var newDigits := digits[i := digits[j]][j := digits[i]];
    
    var left := i + 1;
    var right := |newDigits| - 1;
    while left < right
        invariant 0 <= left <= right + 1 <= |newDigits|
        invariant |newDigits| == |digits|
        invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
    {
        newDigits := newDigits[left := newDigits[right]][right := newDigits[left]];
        left := left + 1;
        right := right - 1;
    }
    
    var newNum := 0;
    var k := 0;
    while k < |newDigits|
        invariant 0 <= k <= |newDigits|
        invariant newNum >= 0
        invariant newNum <= 2147483647
        invariant forall idx :: 0 <= idx < |newDigits| ==> 0 <= newDigits[idx] <= 9
    {
        if newNum > 214748364 || (newNum == 214748364 && newDigits[k] > 7) {
            result := -1;
            return;
        }
        newNum := newNum * 10 + newDigits[k];
        k := k + 1;
    }
    
    if newNum <= n {
        result := -1;
    } else {
        result := newNum;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 0 <= o <= 100000000
    ensures result == -1 || result >= 1
{
    var o1 := maximumSwap_670(o);
    
    if o1 < 1 || o1 > 10000 {
        result := -1;
        return;
    }
    
    var o2 := countLargestGroup_1399(o1);
    
    if o2 < 1 || o2 > 100000000 {
        result := -1;
        return;
    }
    
    var o3 := maxDiff_1432(o2);
    
    if o3 < 1 {
        result := -1;
        return;
    }
    
    var o4 := nextGreaterElement_556(o3);
    result := o4;
}
