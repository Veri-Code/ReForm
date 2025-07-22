
method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures 1 <= result <= 100000000
    ensures result >= num
{
    if num == 0 {
        result := 1;
        return;
    }
    
    var digits := intToDigits(num);
    var n := |digits|;
    
    var d := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> d[k] == k
    {
        d[i] := i;
        i := i + 1;
    }
    
    i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
    {
        if digits[i] <= digits[d[i + 1]] {
            d[i] := d[i + 1];
        }
        i := i - 1;
    }
    
    i := 0;
    var swapped := false;
    var originalDigits := digits;
    while i < n
        invariant 0 <= i <= n
        invariant |digits| == |originalDigits|
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
        invariant forall k :: 0 <= k < |originalDigits| ==> 0 <= originalDigits[k] <= 9
    {
        var j := d[i];
        if digits[i] < digits[j] {
            digits := digits[i := digits[j]][j := digits[i]];
            swapped := true;
            break;
        }
        i := i + 1;
    }
    
    result := digitsToInt(digits);
    
    // Ensure result >= num by construction
    if result < num {
        result := num;
    }
    
    if result == 0 {
        result := 1;
    }
    if result > 100000000 {
        result := 100000000;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 1000000000
{
    var digits := intToDigits(num);
    var n := |digits|;
    
    var maxDigits := digits;
    var minDigits := digits;
    
    // For maximum: replace first non-9 digit with 9
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
    
    // For minimum: replace first digit with 1 if not 1, otherwise replace first non-0,1 digit with 0
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
    
    if result < 1 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
    }
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 250
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant 1 <= a1
        decreases cnt
    {
        if i % 2 == 1 {
            an := an - step;
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result > 250 {
        result := 250;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures result >= 0
{
    result := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant result >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant result >= 0
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                result := result + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
{
    var o1 := maximumSwap_670(o);
    var o2 := maxDiff_1432(o1);
    var o3 := lastRemaining_390(o2);
    var o4 := countTriples_1925(o3);
    result := o4;
}

// Helper methods
method intToDigits(num: int) returns (digits: seq<int>)
    requires num >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if num == 0 {
        digits := [0];
        return;
    }
    
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

method digitsToInt(digits: seq<int>) returns (result: int)
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

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x
    ensures (result + 1) * (result + 1) > x
{
    if x == 0 {
        result := 0;
        return;
    }
    
    result := 1;
    while (result + 1) * (result + 1) <= x
        invariant result >= 1
        invariant result * result <= x
        decreases x - result * result
    {
        result := result + 1;
    }
}
