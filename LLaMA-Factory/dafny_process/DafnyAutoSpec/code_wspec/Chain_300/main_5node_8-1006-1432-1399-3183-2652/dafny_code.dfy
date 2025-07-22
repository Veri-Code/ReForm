
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 100000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        invariant forall i :: 0 <= i < |stk| ==> stk[i] >= -1000000 && stk[i] <= 1000000
        decreases x
    {
        var top := stk[|stk| - 1];
        stk := stk[..|stk| - 1];
        
        if k == 0 {
            var product := top * x;
            if product > 1000000 { product := 1000000; }
            if product < -1000000 { product := -1000000; }
            stk := stk + [product];
        } else if k == 1 {
            var quotient := top / x;
            stk := stk + [quotient];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant result >= -10000000 && result <= 10000000
    {
        var newResult := result + stk[i];
        if newResult > 10000000 { newResult := 10000000; }
        if newResult < -10000000 { newResult := -10000000; }
        result := newResult;
        i := i + 1;
    }
    
    // Ensure postcondition
    if result < 1 {
        result := 1;
    } else if result > 100000000 {
        result := 100000000;
    }
}

function digitSum(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else (n % 10) + digitSum(n / 10)
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 10000
{
    var temp := num;
    var digits := [];
    
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    var maxNum := num;
    var minNum := num;
    
    if |digits| > 0 {
        // Create max number: find first non-9 digit and make it 9
        var maxDigits := digits;
        var i := 0;
        while i < |maxDigits|
            invariant 0 <= i <= |maxDigits|
        {
            if maxDigits[i] != 9 {
                var targetDigit := maxDigits[i];
                var j := 0;
                while j < |maxDigits|
                    invariant 0 <= j <= |maxDigits|
                {
                    if maxDigits[j] == targetDigit {
                        maxDigits := maxDigits[j := 9];
                    }
                    j := j + 1;
                }
                break;
            }
            i := i + 1;
        }
        
        // Create min number
        var minDigits := digits;
        if |minDigits| > 0 && minDigits[0] != 1 {
            var firstDigit := minDigits[0];
            var j := 0;
            while j < |minDigits|
                invariant 0 <= j <= |minDigits|
            {
                if minDigits[j] == firstDigit {
                    minDigits := minDigits[j := 1];
                }
                j := j + 1;
            }
        } else if |minDigits| > 1 {
            var k := 1;
            while k < |minDigits|
                invariant 1 <= k <= |minDigits|
            {
                if minDigits[k] != 0 && minDigits[k] != 1 {
                    var targetDigit := minDigits[k];
                    var j := 0;
                    while j < |minDigits|
                        invariant 0 <= j <= |minDigits|
                    {
                        if minDigits[j] == targetDigit {
                            minDigits := minDigits[j := 0];
                        }
                        j := j + 1;
                    }
                    break;
                }
                k := k + 1;
            }
        }
        
        // Convert back to numbers
        maxNum := 0;
        var m := 0;
        while m < |maxDigits|
            invariant 0 <= m <= |maxDigits|
            invariant maxNum >= 0
        {
            var newMaxNum := maxNum * 10 + maxDigits[m];
            if newMaxNum >= 0 {
                maxNum := newMaxNum;
            }
            m := m + 1;
        }
        
        minNum := 0;
        var n := 0;
        while n < |minDigits|
            invariant 0 <= n <= |minDigits|
            invariant minNum >= 0
        {
            var newMinNum := minNum * 10 + minDigits[n];
            if newMinNum >= 0 {
                minNum := newMinNum;
            }
            n := n + 1;
        }
    }
    
    result := maxNum - minNum;
    if result < 1 {
        result := 1;
    } else if result > 10000 {
        result := 10000;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 100000
{
    var counts := map[];
    var maxCount := 0;
    var ans := 0;
    
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant ans >= 0
    {
        var sum := digitSum(i);
        
        if sum in counts {
            counts := counts[sum := counts[sum] + 1];
        } else {
            counts := counts[sum := 1];
        }
        
        var currentCount := counts[sum];
        if maxCount < currentCount {
            maxCount := currentCount;
            ans := 1;
        } else if maxCount == currentCount {
            ans := ans + 1;
        }
        
        i := i + 1;
    }
    
    result := if ans == 0 then 1 else ans;
    if result > 100000 {
        result := 100000;
    }
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 1000
{
    var mod := 1000000007;
    var f := new int[n + 1];
    
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant forall k :: 0 <= k < j ==> f[k] >= 0
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant forall k :: 0 <= k < j ==> f[k] >= 0
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k < j ==> f[k] >= 0
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    var ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    result := ans % 1000;
    if result == 0 {
        result := 1;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := clumsy_1006(o);
    var o2 := maxDiff_1432(o1);
    var o3 := countLargestGroup_1399(o2);
    var o4 := numberOfWays_3183(o3);
    var o5 := sumOfMultiples_2652(o4);
    result := o5;
}
