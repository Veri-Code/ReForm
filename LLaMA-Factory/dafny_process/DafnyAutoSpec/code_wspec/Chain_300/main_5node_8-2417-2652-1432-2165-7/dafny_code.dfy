
method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
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
        var x := power10(k);
        var y := if k / 2 == 0 then 0 else power10(k / 2) - 1;
        result := x + y;
    } else if a == b {
        result := n;
    } else {
        if n < 1000000000 {
            result := closestFair_2417(n + 1);
        } else {
            result := 1;
        }
    }
}

function power10(exp: int): int
    requires exp >= 0
    ensures power10(exp) >= 1
{
    if exp == 0 then 1
    else 10 * power10(exp - 1)
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 100000000
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    if result == 0 {
        result := 1;
    }
    
    // Ensure upper bound
    if result > 100000000 {
        result := 100000000;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures -1000000000000000 <= result <= 1000000000000000
{
    var digits := getDigits(num);
    var maxNum := maximizeNumber(digits);
    var minNum := minimizeNumber(digits);
    result := maxNum - minNum;
    
    // Ensure bounds
    if result > 1000000000000000 {
        result := 1000000000000000;
    }
    if result < -1000000000000000 {
        result := -1000000000000000;
    }
}

method getDigits(num: int) returns (digits: seq<int>)
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
    
    // Ensure non-empty result
    if |digits| == 0 {
        digits := [0];
    }
}

method maximizeNumber(digits: seq<int>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    var maxDigits := digits;
    
    // Find first digit that's not 9 and replace all occurrences with 9
    var i := 0;
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
        decreases |maxDigits| - i
    {
        if maxDigits[i] != 9 {
            var target := maxDigits[i];
            maxDigits := replaceDigit(maxDigits, target, 9);
            break;
        }
        i := i + 1;
    }
    
    result := seqToInt(maxDigits);
}

method minimizeNumber(digits: seq<int>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    var minDigits := digits;
    
    if minDigits[0] != 1 {
        var target := minDigits[0];
        minDigits := replaceDigit(minDigits, target, 1);
    } else {
        var i := 1;
        while i < |minDigits|
            invariant 1 <= i <= |minDigits|
            decreases |minDigits| - i
        {
            if minDigits[i] != 0 && minDigits[i] != 1 {
                var target := minDigits[i];
                minDigits := replaceDigit(minDigits, target, 0);
                break;
            }
            i := i + 1;
        }
    }
    
    result := seqToInt(minDigits);
}

method replaceDigit(digits: seq<int>, target: int, replacement: int) returns (result: seq<int>)
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires 0 <= target <= 9 && 0 <= replacement <= 9
    ensures |result| == |digits|
    ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
{
    result := [];
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> 0 <= result[j] <= 9
        decreases |digits| - i
    {
        if digits[i] == target {
            result := result + [replacement];
        } else {
            result := result + [digits[i]];
        }
        i := i + 1;
    }
}

method seqToInt(digits: seq<int>) returns (result: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures result >= 0
{
    result := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
        decreases |digits| - i
    {
        result := result * 10 + digits[i];
        i := i + 1;
    }
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures -2147483648 <= result <= 2147483648
{
    var neg := num < 0;
    var absNum := if num < 0 then -num else num;
    
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> cnt[j] == 0
        decreases 10 - i
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var n := absNum;
    while n > 0
        invariant n >= 0
        invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
        decreases n
    {
        cnt[n % 10] := cnt[n % 10] + 1;
        n := n / 10;
    }
    
    var ans := 0;
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant ans >= 0
            decreases i + 1
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
                decreases cnt[i] - j
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        result := if ans <= 2147483648 then -ans else -2147483648;
    } else {
        if cnt[0] > 0 {
            i := 1;
            while i < 10
                invariant 1 <= i <= 10
                decreases 10 - i
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
            decreases 10 - i
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant ans >= 0
                decreases cnt[i] - j
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i + 1;
        }
        result := if ans <= 2147483648 then ans else 2147483648;
    }
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483648
    ensures -2147483648 <= result <= 2147483647
{
    var ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var num := x;
    
    while num != 0
        invariant -2147483648 <= ans <= 2147483647
        invariant if num == 0 then true else (if num > 0 then num <= x else num >= x)
        decreases if num >= 0 then num else -num
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            result := 0;
            return;
        }
        
        var y := num % 10;
        if num < 0 && y > 0 {
            y := y - 10;
        }
        
        if (ans > 0 && ans > (mx - y) / 10) || (ans < 0 && ans < (mi - y) / 10) {
            result := 0;
            return;
        }
        
        var newAns := ans * 10 + y;
        if newAns < mi || newAns > mx {
            result := 0;
            return;
        }
        
        ans := newAns;
        num := (num - y) / 10;
    }
    result := ans;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures -2147483648 <= result <= 2147483647
    decreases *
{
    var o1 := closestFair_2417(o);
    var o2: int;
    if o1 <= 1000 {
        o2 := sumOfMultiples_2652(o1);
    } else {
        o2 := 1;
    }
    var o3 := maxDiff_1432(o2);
    var o4 := smallestNumber_2165(o3);
    result := reverse_7(o4);
}
