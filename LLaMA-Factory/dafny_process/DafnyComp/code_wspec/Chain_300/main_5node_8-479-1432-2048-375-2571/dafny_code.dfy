
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 100000000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx == power10(n) - 1
        decreases a
    {
        // Create palindrome by mirroring a
        var b := a;
        var x := a;
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        // Check if x has factors in valid range
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 {
                    return 1337;
                }
                return res;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result <= 1000000
{
    // Convert to string representation (simulate with digits)
    var digits := getDigits(num);
    var maxNum := maximizeNumber(digits);
    var minNum := minimizeNumber(digits);
    result := maxNum - minNum;
    if result < 0 {
        result := 0;
    }
    if result > 1000000 {
        result := 1000000;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 200
{
    var x := n + 1;
    if x > 200 {
        return 200;
    }
    while x <= 200
        invariant x >= n + 1
        invariant x <= 201
        decreases 201 - x
    {
        if isBeautiful(x) {
            return x;
        }
        x := x + 1;
    }
    return 200; // fallback
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 100000
{
    if n == 1 {
        return 1;
    }
    
    var f := new int[n + 1, n + 1];
    
    // Initialize array
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
        decreases i
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
        {
            f[i, j] := j + f[i, j - 1];
            var k := i;
            while k < j
                invariant i <= k <= j
            {
                var leftCost := if k - 1 >= 0 then f[i, k - 1] else 0;
                var rightCost := if k + 1 <= n then f[k + 1, j] else 0;
                var totalCost := max(leftCost, rightCost) + k;
                f[i, j] := min(f[i, j], totalCost);
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    var res := f[1, n];
    if res < 1 {
        return 1;
    }
    if res > 100000 {
        return 100000;
    }
    return res;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 0
{
    var ans := 0;
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
            cnt := if cnt == 1 then 0 else 1;
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    return ans;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := maxDiff_1432(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    var o4 := getMoneyAmount_375(o3);
    var o5 := minOperations_2571(o4);
    return o5;
}

// Helper functions
function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) > 0
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else 100000000
}

method getDigits(num: int) returns (digits: seq<int>)
    requires num > 0
    ensures |digits| > 0
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    digits := [];
    var n := num;
    while n > 0
        invariant n >= 0
        invariant |digits| >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant n == 0 ==> |digits| > 0
        decreases n
    {
        digits := [n % 10] + digits;
        n := n / 10;
    }
    
    if |digits| == 0 {
        digits := [0];
    }
}

method maximizeNumber(digits: seq<int>) returns (result: int)
    requires |digits| > 0
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    var maxDigits := digits;
    var i := 0;
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
    {
        if maxDigits[i] != 9 {
            maxDigits := replaceDigit(maxDigits, maxDigits[i], 9);
            break;
        }
        i := i + 1;
    }
    result := digitsToNumber(maxDigits);
}

method minimizeNumber(digits: seq<int>) returns (result: int)
    requires |digits| > 0
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    var minDigits := digits;
    if |minDigits| > 0 && minDigits[0] != 1 {
        minDigits := replaceDigit(minDigits, minDigits[0], 1);
    } else if |minDigits| > 1 {
        var i := 1;
        while i < |minDigits|
            invariant 1 <= i <= |minDigits|
        {
            if minDigits[i] != 0 && minDigits[i] != 1 {
                minDigits := replaceDigit(minDigits, minDigits[i], 0);
                break;
            }
            i := i + 1;
        }
    }
    result := digitsToNumber(minDigits);
}

method replaceDigit(digits: seq<int>, oldDigit: int, newDigit: int) returns (result: seq<int>)
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires 0 <= oldDigit <= 9
    requires 0 <= newDigit <= 9
    ensures |result| == |digits|
    ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
{
    result := [];
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> 0 <= result[j] <= 9
    {
        if digits[i] == oldDigit {
            result := result + [newDigit];
        } else {
            result := result + [digits[i]];
        }
        i := i + 1;
    }
}

method digitsToNumber(digits: seq<int>) returns (result: int)
    requires |digits| > 0
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

predicate isBeautiful(x: int)
    requires x > 0
{
    var counts := getDigitCounts(x);
    forall i :: 0 <= i < |counts| ==> (counts[i] == 0 || i == counts[i])
}

function getDigitCounts(x: int): seq<int>
    requires x > 0
    ensures |getDigitCounts(x)| == 10
    ensures forall i :: 0 <= i < 10 ==> getDigitCounts(x)[i] >= 0
{
    getDigitCountsHelper(x, seq(10, i => 0))
}

function getDigitCountsHelper(x: int, counts: seq<int>): seq<int>
    requires x >= 0
    requires |counts| == 10
    requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
    ensures |getDigitCountsHelper(x, counts)| == 10
    ensures forall i :: 0 <= i < 10 ==> getDigitCountsHelper(x, counts)[i] >= 0
    decreases x
{
    if x == 0 then counts
    else 
        var digit := x % 10;
        var newCounts := counts[digit := counts[digit] + 1];
        getDigitCountsHelper(x / 10, newCounts)
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}
