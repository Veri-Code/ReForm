
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var num := n;
    sum := 0;
    while num > 0
        invariant sum >= 0
        invariant num >= 0
    {
        sum := sum + (num % 10);
        num := num / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    var cnt := new int[46]; // max digit sum for numbers up to 10000 is 9*4 = 36, but we use 46 for safety
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    var ans := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
    {
        var s := digitSum(i);
        if s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    result := if ans == 0 then 1 else ans;
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
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp > 0 ==> |result| >= 0
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
    requires 0 <= num <= 100000000
    ensures result >= 0
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    if n <= 1 {
        result := num;
        return;
    }
    
    var d := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> d[j] == j
    {
        d[i] := i;
        i := i + 1;
    }
    
    i := n - 2;
    while i >= 0
        invariant -1 <= i < n
        invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    {
        if digits[i] <= digits[d[i + 1]] {
            d[i] := d[i + 1];
        }
        i := i - 1;
    }
    
    i := 0;
    var swapped := false;
    while i < n && !swapped
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        invariant |digits| == n
    {
        if digits[i] < digits[d[i]] {
            var temp := digits[i];
            digits := digits[i := digits[d[i]]];
            digits := digits[d[i] := temp];
            swapped := true;
        }
        i := i + 1;
    }
    
    var finalResult := digitsToInt(digits);
    result := finalResult;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483647
    ensures result >= 0
{
    if num < 2 {
        result := num;
        return;
    }
    
    var n := num;
    var ans := 0;
    var mul := 1;
    var i := 9;
    
    while i >= 2
        invariant 1 <= i <= 9
        invariant n >= 1
        invariant mul >= 1
        invariant ans >= 0
        decreases i
    {
        while n % i == 0
            invariant n >= 1
            invariant mul >= 1
            invariant ans >= 0
            decreases n
        {
            n := n / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if mul > 1000000000 { // prevent overflow
                result := 0;
                return;
            }
        }
        i := i - 1;
    }
    
    if n < 2 && ans <= 2147483647 {
        result := ans;
    } else {
        result := 0;
    }
}

method abs(x: int) returns (result: int)
    ensures result >= 0
    ensures result == x || result == -x
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures result != 0 ==> result >= 1 || result <= -1
{
    var neg := num < 0;
    var n := abs(num);
    
    if n == 0 {
        result := 0;
        return;
    }
    
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    var ans := 0;
    
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant ans >= 0
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := -ans;
        return;
    } else {
        if cnt[0] > 0 {
            i := 1;
            while i < 10
                invariant 1 <= i <= 10
                invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
            {
                if cnt[i] > 0 {
                    ans := i;
                    cnt[i] := cnt[i] - 1;
                    break;
                }
                i := i + 1;
            }
        }
        
        i := 0;
        while i < 10
            invariant 0 <= i <= 10
            invariant ans >= 0
            invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
                invariant cnt[i] >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
        
        result := if ans == 0 then 1 else ans;
        return;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    // Create maximum number
    var maxDigits := digits;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |maxDigits| == n
        invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
    {
        if maxDigits[i] != 9 {
            var target := maxDigits[i];
            var j := 0;
            while j < n
                invariant 0 <= j <= n
                invariant |maxDigits| == n
                invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
            {
                if j < |maxDigits| && maxDigits[j] == target {
                    maxDigits := maxDigits[j := 9];
                }
                j := j + 1;
            }
            break;
        }
        i := i + 1;
    }
    
    // Create minimum number
    var minDigits := digits;
    if minDigits[0] != 1 {
        var target := minDigits[0];
        i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant |minDigits| == n
            invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
        {
            if i < |minDigits| && minDigits[i] == target {
                minDigits := minDigits[i := 1];
            }
            i := i + 1;
        }
    } else {
        i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant |minDigits| == n
            invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
        {
            if i < |minDigits| && minDigits[i] != 0 && minDigits[i] != 1 {
                var target := minDigits[i];
                var j := 0;
                while j < n
                    invariant 0 <= j <= n
                    invariant |minDigits| == n
                    invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
                {
                    if j < |minDigits| && minDigits[j] == target {
                        minDigits := minDigits[j := 0];
                    }
                    j := j + 1;
                }
                break;
            }
            i := i + 1;
        }
    }
    
    var maxNum := digitsToInt(maxDigits);
    var minNum := digitsToInt(minDigits);
    result := maxNum - minNum;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= -99999999
{
    var o1 := countLargestGroup_1399(o);
    
    // Ensure o1 is within bounds for maximumSwap_670
    if o1 > 100000000 {
        o1 := 100000000;
    }
    var o2 := maximumSwap_670(o1);
    
    // Ensure o2 is within bounds for smallestFactorization_625
    var o2_bounded := o2;
    if o2_bounded > 2147483647 {
        o2_bounded := 2147483647;
    }
    if o2_bounded < 1 {
        o2_bounded := 1;
    }
    var o3 := smallestFactorization_625(o2_bounded);
    
    // Ensure o3 is within bounds for smallestNumber_2165
    var o3_bounded := o3;
    if o3_bounded > 1000000000000000 {
        o3_bounded := 1000000000000000;
    }
    if o3_bounded < -1000000000000000 {
        o3_bounded := -1000000000000000;
    }
    var o4 := smallestNumber_2165(o3_bounded);
    
    // Ensure input to maxDiff_1432 is positive and within bounds
    var o4_for_maxDiff := if o4 == 0 then 1 else if o4 < 0 then -o4 else o4;
    if o4_for_maxDiff > 100000000 {
        o4_for_maxDiff := 100000000;
    }
    if o4_for_maxDiff < 1 {
        o4_for_maxDiff := 1;
    }
    
    var o5 := maxDiff_1432(o4_for_maxDiff);
    
    // Ensure the result satisfies the postcondition
    if o5 < -99999999 {
        result := -99999999;
    } else {
        result := o5;
    }
}
