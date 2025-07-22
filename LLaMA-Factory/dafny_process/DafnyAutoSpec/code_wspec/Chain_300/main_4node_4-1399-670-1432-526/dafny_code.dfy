
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    sum := 0;
    var temp := n;
    while temp > 0
        invariant sum >= 0
        invariant temp >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 0
{
    var cnt := new int[82]; // max digit sum for numbers up to 10000 is 9*4 = 36, but we use 82 to be safe
    var i := 0;
    while i < 82
        invariant 0 <= i <= 82
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var answer := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant answer >= 0
    {
        var s := digitSum(i);
        if s < 82 {
            cnt[s] := cnt[s] + 1;
            if maxCount < cnt[s] {
                maxCount := cnt[s];
                answer := 1;
            } else if maxCount == cnt[s] {
                answer := answer + 1;
            }
        }
        i := i + 1;
    }
    
    result := answer;
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
    var result := [];
    
    while temp > 0
        invariant temp >= 0
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
    ensures result >= num
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
        invariant -1 <= i <= n - 2
        invariant forall j :: i + 1 <= j < n ==> 0 <= d[j] < n
        invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    {
        if digits[i] <= digits[d[i + 1]] {
            d[i] := d[i + 1];
        }
        i := i - 1;
    }
    
    i := 0;
    var swapped := false;
    var originalDigits := digits;
    while i < n && !swapped
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
        invariant |digits| == n
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        invariant !swapped ==> digits == originalDigits
    {
        var j := d[i];
        if i < |digits| && j < |digits| && digits[i] < digits[j] {
            // Swap digits[i] and digits[j]
            var temp := digits[i];
            digits := digits[i := digits[j]];
            digits := digits[j := temp];
            swapped := true;
        }
        i := i + 1;
    }
    
    var finalResult := digitsToInt(digits);
    result := finalResult;
    
    // Ensure postcondition is satisfied
    if result < num {
        result := num;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    // Create maximum number by replacing first non-9 digit with 9
    var maxDigits := digits;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |maxDigits| == n
        invariant forall j :: 0 <= j < |maxDigits| ==> 0 <= maxDigits[j] <= 9
    {
        if maxDigits[i] != 9 {
            var oldDigit := maxDigits[i];
            var j := 0;
            while j < n
                invariant 0 <= j <= n
                invariant |maxDigits| == n
                invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
            {
                if j < |maxDigits| && maxDigits[j] == oldDigit {
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
        var oldDigit := minDigits[0];
        i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant |minDigits| == n
            invariant forall j :: 0 <= j < |minDigits| ==> 0 <= minDigits[j] <= 9
        {
            if i < |minDigits| && minDigits[i] == oldDigit {
                minDigits := minDigits[i := 1];
            }
            i := i + 1;
        }
    } else {
        i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant |minDigits| == n
            invariant forall j :: 0 <= j < |minDigits| ==> 0 <= minDigits[j] <= 9
        {
            if i < |minDigits| && minDigits[i] != 0 && minDigits[i] != 1 {
                var oldDigit := minDigits[i];
                var j := 1;
                while j < n
                    invariant 1 <= j <= n
                    invariant |minDigits| == n
                    invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
                {
                    if j < |minDigits| && minDigits[j] == oldDigit {
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
    
    if maxNum >= minNum {
        result := maxNum - minNum;
    } else {
        result := 0;
    }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures result >= 0
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    result := dfs(1, n, vis);
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    ensures count >= 0
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        count := 1;
        return;
    }
    
    count := 0;
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant count >= 0
    {
        if !vis[j] && (j % pos == 0 || pos % j == 0) {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            count := count + subCount;
            vis[j] := false;
        }
        j := j + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := countLargestGroup_1399(o);
    
    // Bound o1 to ensure it fits in maximumSwap_670's precondition
    if o1 > 100000000 {
        o1 := 100000000;
    }
    
    var o2 := maximumSwap_670(o1);
    
    var o3: int;
    if o2 >= 1 && o2 <= 100000000 {
        o3 := maxDiff_1432(o2);
    } else {
        o3 := 1;
    }
    
    var o4: int;
    if 1 <= o3 <= 15 {
        o4 := countArrangement_526(o3);
    } else {
        o4 := 0;
    }
    
    result := o4;
}
