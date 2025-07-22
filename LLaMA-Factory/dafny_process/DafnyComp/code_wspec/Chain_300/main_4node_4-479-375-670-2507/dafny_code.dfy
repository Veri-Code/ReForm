
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 200
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        invariant mx == power10(n) - 1
        decreases a
    {
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
        
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            invariant mx == power10(n) - 1
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 { res := 1337; }
                if res > 200 { res := 200; }
                return res;
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    return 9;
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 0 <= result <= 100000000
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var row := 0;
    while row <= n
        invariant 0 <= row <= n + 1
        invariant f.Length0 == n + 1 && f.Length1 == n + 1
    {
        var col := 0;
        while col <= n
            invariant 0 <= col <= n + 1
            invariant row < f.Length0
        {
            f[row, col] := 0;
            col := col + 1;
        }
        row := row + 1;
    }
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
        invariant f.Length0 == n + 1 && f.Length1 == n + 1
        decreases i
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant 0 <= i < f.Length0
            invariant f.Length0 == n + 1 && f.Length1 == n + 1
        {
            f[i, j] := j + f[i, j - 1];
            
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant 0 <= i < f.Length0 && j < f.Length1
                invariant f.Length0 == n + 1 && f.Length1 == n + 1
            {
                var val1 := if k - 1 >= 0 then f[i, k - 1] else 0;
                var val2 := if k + 1 <= n then f[k + 1, j] else 0;
                var maxVal := if val1 > val2 then val1 else val2;
                var newVal := maxVal + k;
                if newVal < f[i, j] {
                    f[i, j] := newVal;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    var res := f[1, n];
    if res < 0 { res := 0; }
    if res > 100000000 { res := 100000000; }
    return res;
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures 2 <= result <= 100000
{
    if num < 2 {
        return 2;
    }
    
    var digits := intToDigits(num);
    var n := |digits|;
    
    if n == 0 {
        return 2;
    }
    
    var d := new int[n];
    var idx := 0;
    while idx < n
        invariant 0 <= idx <= n
        invariant d.Length == n
        invariant forall k :: 0 <= k < idx ==> d[k] == k
    {
        d[idx] := idx;
        idx := idx + 1;
    }
    
    var i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant d.Length == n
        invariant |digits| == n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
        decreases i + 1
    {
        if i + 1 < n && d[i + 1] < n {
            if digits[i] <= digits[d[i + 1]] {
                d[i] := d[i + 1];
            }
        }
        i := i - 1;
    }
    
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant d.Length == n
        invariant |digits| == n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        if d[j] < n && digits[j] < digits[d[j]] {
            var temp := digits[j];
            digits := digits[j := digits[d[j]]];
            digits := digits[d[j] := temp];
            break;
        }
        j := j + 1;
    }
    
    var resultVal := digitsToInt(digits);
    if resultVal < 2 {
        return 2;
    }
    if resultVal > 100000 {
        return 100000;
    }
    return resultVal;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 1
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 1
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp_current := current;
        
        while i <= temp_current / i && i <= temp_current
            invariant i >= 2
            invariant s >= 0
            invariant temp_current >= 1
            decreases temp_current - i + 1
        {
            while temp_current % i == 0 && temp_current > 1
                invariant temp_current >= 1
                invariant i >= 2
                invariant s >= 0
                decreases temp_current
            {
                temp_current := temp_current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp_current > 1 {
            s := s + temp_current;
        }
        
        if s == t {
            return t;
        }
        
        current := if s >= 1 then s else 1;
        iterations := iterations + 1;
    }
    
    return current;
}

function power10(n: int): int
    requires 0 <= n <= 10
    ensures power10(n) >= 1
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else if n == 8 then 100000000
    else 1000000000
}

method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if num == 0 {
        return [0];
    }
    
    var result: seq<int> := [];
    var n := num;
    
    while n > 0
        invariant n >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        decreases n
    {
        result := [n % 10] + result;
        n := n / 10;
    }
    
    if |result| == 0 {
        result := [0];
    }
    
    return result;
}

method digitsToInt(digits: seq<int>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    var res := 0;
    var i := 0;
    
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant res >= 0
    {
        res := res * 10 + digits[i];
        i := i + 1;
    }
    
    return res;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 1
{
    var o1 := largestPalindrome_479(o);
    var o2 := getMoneyAmount_375(o1);
    var o3 := maximumSwap_670(o2);
    var o4 := smallestValue_2507(o3);
    return o4;
}
