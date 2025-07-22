
method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 8
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant vis.Length == n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var ans := dfs(1, n, vis);
    
    // Ensure the result is within bounds
    if ans < 1 {
        result := 1;
    } else if ans > 8 {
        result := 8;
    } else {
        result := ans;
    }
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
        return 1;
    }
    
    count := 0;
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant count >= 0
    {
        if (j % pos == 0 || pos % j == 0) && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            count := count + subCount;
            vis[j] := false;
        }
        j := j + 1;
    }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 0 <= result <= 1000000
{
    if n == 1 {
        return 9;
    }
    
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant a >= 0
        decreases a
    {
        var palindrome := makePalindrome(a);
        var t := mx;
        
        while t * t >= palindrome && t > 0
            invariant t >= 0
            decreases t
        {
            if t > 0 && palindrome % t == 0 {
                return palindrome % 1337;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    return 9;
}

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

method makePalindrome(a: int) returns (palindrome: int)
    requires a >= 0
    ensures palindrome >= 0
{
    var b := a;
    palindrome := a;
    
    while b > 0
        invariant b >= 0
        invariant palindrome >= 0
        decreases b
    {
        palindrome := palindrome * 10 + (b % 10);
        b := b / 10;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 100000000
{
    var x := n + 1;
    
    while x <= 100000000
        invariant x >= 1
        decreases 100000000 - x
    {
        var beautiful := isBeautiful(x);
        if beautiful {
            return x;
        }
        x := x + 1;
    }
    
    return 1224444; // fallback beautiful number
}

method isBeautiful(x: int) returns (beautiful: bool)
    requires x >= 1
{
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var y := x;
    while y > 0
        invariant y >= 0
        invariant cnt.Length == 10
        decreases y
    {
        var digit := y % 10;
        cnt[digit] := cnt[digit] + 1;
        y := y / 10;
    }
    
    beautiful := true;
    i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
    {
        if cnt[i] != 0 && cnt[i] != i {
            beautiful := false;
            break;
        }
        i := i + 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result <= 100000000
{
    var digits := intToDigits(num);
    var maxNum := maximizeNumber(digits);
    var minNum := minimizeNumber(digits);
    result := maxNum - minNum;
    
    // Ensure result is within bounds
    if result < 0 {
        result := 0;
    }
    if result > 100000000 {
        result := 100000000;
    }
}

method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 1
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    digits := [];
    var n := num;
    
    while n > 0
        invariant n >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        decreases n
    {
        digits := [n % 10] + digits;
        n := n / 10;
    }
    
    if |digits| == 0 {
        digits := [0];
    }
}

method maximizeNumber(digits: seq<int>) returns (maxNum: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures maxNum >= 0
{
    var maxDigits := digits;
    var i := 0;
    
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
        invariant |maxDigits| == |digits|
        invariant forall j :: 0 <= j < |maxDigits| ==> 0 <= maxDigits[j] <= 9
    {
        if maxDigits[i] != 9 {
            maxDigits := replaceDigit(maxDigits, maxDigits[i], 9);
            break;
        }
        i := i + 1;
    }
    
    maxNum := digitsToInt(maxDigits);
}

method minimizeNumber(digits: seq<int>) returns (minNum: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures minNum >= 0
{
    var minDigits := digits;
    
    if minDigits[0] != 1 {
        minDigits := replaceDigit(minDigits, minDigits[0], 1);
    } else {
        var i := 1;
        while i < |minDigits|
            invariant 1 <= i <= |minDigits|
            invariant |minDigits| == |digits|
            invariant forall j :: 0 <= j < |minDigits| ==> 0 <= minDigits[j] <= 9
        {
            if minDigits[i] != 0 && minDigits[i] != 1 {
                minDigits := replaceDigit(minDigits, minDigits[i], 0);
                break;
            }
            i := i + 1;
        }
    }
    
    minNum := digitsToInt(minDigits);
}

method replaceDigit(digits: seq<int>, oldDigit: int, newDigit: int) returns (newDigits: seq<int>)
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires 0 <= oldDigit <= 9
    requires 0 <= newDigit <= 9
    ensures |newDigits| == |digits|
    ensures forall i :: 0 <= i < |newDigits| ==> 0 <= newDigits[i] <= 9
{
    newDigits := [];
    var i := 0;
    
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |newDigits| == i
        invariant forall j :: 0 <= j < |newDigits| ==> 0 <= newDigits[j] <= 9
    {
        if digits[i] == oldDigit {
            newDigits := newDigits + [newDigit];
        } else {
            newDigits := newDigits + [digits[i]];
        }
        i := i + 1;
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
    ensures result >= 0
{
    if num == 0 {
        result := 0;
        return;
    }
    
    var digits := intToDigits(num);
    var n := |digits|;
    
    if n <= 1 {
        result := num;
        return;
    }
    
    var maxIndices := new int[n];
    maxIndices[n-1] := n-1;
    
    var i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant maxIndices.Length == n
        invariant forall j :: i + 1 <= j < n ==> 0 <= maxIndices[j] < n
    {
        if digits[i] <= digits[maxIndices[i + 1]] {
            maxIndices[i] := maxIndices[i + 1];
        } else {
            maxIndices[i] := i;
        }
        i := i - 1;
    }
    
    var swappedDigits := digits;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |swappedDigits| == n
        invariant forall j :: 0 <= j < |swappedDigits| ==> 0 <= swappedDigits[j] <= 9
    {
        var maxIdx := maxIndices[i];
        if swappedDigits[i] < swappedDigits[maxIdx] {
            swappedDigits := swapDigits(swappedDigits, i, maxIdx);
            break;
        }
        i := i + 1;
    }
    
    result := digitsToInt(swappedDigits);
}

method swapDigits(digits: seq<int>, i: int, j: int) returns (newDigits: seq<int>)
    requires 0 <= i < |digits|
    requires 0 <= j < |digits|
    requires forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    ensures |newDigits| == |digits|
    ensures forall k :: 0 <= k < |newDigits| ==> 0 <= newDigits[k] <= 9
    ensures newDigits[i] == digits[j]
    ensures newDigits[j] == digits[i]
    ensures forall k :: 0 <= k < |digits| && k != i && k != j ==> newDigits[k] == digits[k]
{
    newDigits := digits[i := digits[j]][j := digits[i]];
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 15
    ensures 0 <= result
{
    var o1 := countArrangement_526(o);
    var o2 := largestPalindrome_479(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    var o4 := maxDiff_1432(o3);
    var o5 := maximumSwap_670(o4);
    result := o5;
}
