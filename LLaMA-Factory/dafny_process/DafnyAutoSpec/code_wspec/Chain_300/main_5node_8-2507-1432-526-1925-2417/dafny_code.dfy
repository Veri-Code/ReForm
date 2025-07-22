
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 100000000
    decreases *
{
    var current := n;
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp := current;
        
        while i * i <= temp
            invariant 2 <= i
            invariant s >= 0
            invariant temp >= 0
        {
            while temp % i == 0 && temp > 0
                invariant temp >= 0
                invariant i >= 2
                invariant s >= 0
                decreases temp
            {
                temp := temp / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            s := s + temp;
        }
        
        if s == t {
            if t >= 1 && t <= 100000000 {
                return t;
            } else {
                return 2;
            }
        }
        current := s;
        if s <= 1 {
            return 2;
        }
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 0 <= result
{
    var digits := [];
    var temp := num;
    
    // Convert to digits
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        result := 0;
        return;
    }
    
    // Find maximum number
    var maxNum := num;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
    {
        if digits[i] != 9 {
            var newDigits := digits[..];
            var j := 0;
            while j < |newDigits|
                invariant 0 <= j <= |newDigits|
                invariant forall k :: 0 <= k < |newDigits| ==> 0 <= newDigits[k] <= 9
            {
                if newDigits[j] == digits[i] {
                    newDigits := newDigits[j := 9];
                }
                j := j + 1;
            }
            maxNum := digitsToInt(newDigits);
            break;
        }
        i := i + 1;
    }
    
    // Find minimum number
    var minNum := num;
    if |digits| > 0 && digits[0] != 1 {
        var newDigits := digits[..];
        var j := 0;
        while j < |newDigits|
            invariant 0 <= j <= |newDigits|
            invariant forall k :: 0 <= k < |newDigits| ==> 0 <= newDigits[k] <= 9
        {
            if newDigits[j] == digits[0] {
                newDigits := newDigits[j := 1];
            }
            j := j + 1;
        }
        minNum := digitsToInt(newDigits);
    } else if |digits| > 1 {
        var i := 1;
        while i < |digits|
            invariant 1 <= i <= |digits|
            invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
        {
            if digits[i] != 0 && digits[i] != 1 {
                var newDigits := digits[..];
                var j := 0;
                while j < |newDigits|
                    invariant 0 <= j <= |newDigits|
                    invariant forall k :: 0 <= k < |newDigits| ==> 0 <= newDigits[k] <= 9
                {
                    if newDigits[j] == digits[i] {
                        newDigits := newDigits[j := 0];
                    }
                    j := j + 1;
                }
                minNum := digitsToInt(newDigits);
                break;
            }
            i := i + 1;
        }
    }
    
    result := if maxNum >= minNum then maxNum - minNum else 0;
}

function digitsToInt(digits: seq<int>): int
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if |digits| == 0 then 0
    else digits[0] * pow10(|digits| - 1) + digitsToInt(digits[1..])
}

function pow10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 250
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
    if result == 0 {
        result := 1;
    }
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    ensures count >= 0
    ensures count <= 250
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
        invariant count <= 250
    {
        if !vis[j] && (j % pos == 0 || pos % j == 0) {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis);
            if count + subCount <= 250 {
                count := count + subCount;
            } else {
                count := 250;
            }
            vis[j] := false;
        }
        j := j + 1;
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

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x < (isqrt(x) + 1) * (isqrt(x) + 1)
{
    if x == 0 then 0
    else if x < 4 then 1
    else
        var guess := isqrt(x / 4) * 2;
        if (guess + 1) * (guess + 1) <= x then guess + 1 else guess
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures result >= 1
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant a >= 0 && b >= 0 && k >= 0
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
        var y := if k / 2 > 0 then (pow10(k / 2) - 1) / 9 else 0;
        result := x + y;
        if result < 1 {
            result := 1;
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

method main_5node_8(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 0
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := maxDiff_1432(o1);
    var o3: int;
    if 1 <= o2 <= 15 {
        o3 := countArrangement_526(o2);
    } else {
        o3 := 1;
    }
    var o4 := countTriples_1925(o3);
    var o5: int;
    if 1 <= o4 <= 1000000000 {
        o5 := closestFair_2417(o4);
    } else {
        o5 := 1;
    }
    result := o5;
}
