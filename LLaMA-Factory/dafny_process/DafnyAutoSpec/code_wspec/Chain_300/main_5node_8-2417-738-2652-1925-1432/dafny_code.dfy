
function pow10(exp: int): int
    requires 0 <= exp <= 10
    ensures pow10(exp) > 0
{
    if exp == 0 then 1
    else 10 * pow10(exp - 1)
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 0 <= result <= 1000000000
    decreases 1000000000 - n
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    // Count digits and odd/even digits
    while t > 0
        invariant 0 <= t <= n
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        invariant k <= 10
        invariant t < pow10(10 - k)
        decreases t
    {
        if (t % 10) % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    if k % 2 == 1 {
        var x := pow10(k);
        var y := if k / 2 == 0 then 0 else pow10(k / 2) - 1;
        result := x + y;
        if result > 1000000000 {
            result := 1000000000;
        }
    } else if a == b {
        result := n;
    } else {
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := n;
        }
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        result := 1;
        return;
    }
    
    var digits := intToDigits(n);
    var i := 1;
    
    // Find first decreasing position
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
        invariant forall j :: 1 <= j < i ==> digits[j-1] <= digits[j]
    {
        i := i + 1;
    }
    
    if i < |digits| {
        // Decrease digits and propagate
        while i > 0 && i < |digits| && digits[i-1] > digits[i]
            invariant 0 <= i < |digits|
            invariant |digits| > 0
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            if digits[i-1] > 0 {
                digits := digits[i-1 := digits[i-1] - 1];
            }
            i := i - 1;
        }
        
        i := i + 1;
        // Set remaining digits to 9
        while i < |digits|
            invariant 0 <= i <= |digits|
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            digits := digits[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(digits);
    if result == 0 {
        result := 1;
    }
    if result > 1000000000 {
        result := 1000000000;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result
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
    
    if result == 0 {
        result := 1;
    }
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 0 <= result
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

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures result >= 0
{
    var digits := intToDigits(num);
    var maxDigits := digits;
    var minDigits := digits;
    
    // Create maximum number
    var i := 0;
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
        invariant forall j :: 0 <= j < |maxDigits| ==> 0 <= maxDigits[j] <= 9
        invariant |maxDigits| > 0
    {
        if maxDigits[i] != 9 {
            var oldDigit := maxDigits[i];
            var j := 0;
            while j < |maxDigits|
                invariant 0 <= j <= |maxDigits|
                invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
                invariant |maxDigits| > 0
            {
                if maxDigits[j] == oldDigit {
                    maxDigits := maxDigits[j := 9];
                }
                j := j + 1;
            }
            break;
        }
        i := i + 1;
    }
    
    // Create minimum number
    if |minDigits| > 0 {
        if minDigits[0] != 1 {
            var oldDigit := minDigits[0];
            var j := 0;
            while j < |minDigits|
                invariant 0 <= j <= |minDigits|
                invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
                invariant |minDigits| > 0
            {
                if minDigits[j] == oldDigit {
                    minDigits := minDigits[j := 1];
                }
                j := j + 1;
            }
        } else {
            var k := 1;
            while k < |minDigits|
                invariant 1 <= k <= |minDigits|
                invariant forall l :: 0 <= l < |minDigits| ==> 0 <= minDigits[l] <= 9
                invariant |minDigits| > 0
            {
                if minDigits[k] != 0 && minDigits[k] != 1 {
                    var oldDigit := minDigits[k];
                    var j := 0;
                    while j < |minDigits|
                        invariant 0 <= j <= |minDigits|
                        invariant forall l :: 0 <= l < |minDigits| ==> 0 <= minDigits[l] <= 9
                        invariant |minDigits| > 0
                    {
                        if minDigits[j] == oldDigit {
                            minDigits := minDigits[j := 0];
                        }
                        j := j + 1;
                    }
                    break;
                }
                k := k + 1;
            }
        }
    }
    
    var maxNum := digitsToInt(maxDigits);
    var minNum := digitsToInt(minDigits);
    result := if maxNum >= minNum then maxNum - minNum else 0;
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        result := 0;
        return;
    }
    
    result := 1;
    while (result + 1) * (result + 1) <= x
        invariant result >= 1
        invariant result * result <= x
    {
        result := result + 1;
    }
}

method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| > 0
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        digits := [0];
        return;
    }
    
    digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant temp > 0 ==> |digits| >= 0
        invariant temp == 0 ==> |digits| > 0
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
}

method digitsToInt(digits: seq<int>) returns (result: int)
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

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 0
{
    var o1 := closestFair_2417(o);
    var o2 := monotoneIncreasingDigits_738(o1);
    
    // Ensure o2 is within bounds for sumOfMultiples_2652
    if o2 > 1000 {
        o2 := 1000;
    }
    var o3 := sumOfMultiples_2652(o2);
    
    // Ensure o3 is within bounds for countTriples_1925
    if o3 > 250 {
        o3 := 250;
    }
    var o4 := countTriples_1925(o3);
    
    // Ensure o4 is within bounds for maxDiff_1432
    if o4 > 100000000 {
        o4 := 100000000;
    }
    if o4 < 1 {
        o4 := 1;
    }
    var o5 := maxDiff_1432(o4);
    result := o5;
}
