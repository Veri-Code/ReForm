
method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000000000
    decreases *
{
    var current := n;
    while true
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        
        while i <= current / i
            invariant 2 <= i
            invariant s >= 0
            invariant current >= 1
        {
            while current % i == 0
                invariant i >= 2
                invariant current >= 1
                invariant s >= 0
                decreases current
            {
                current := current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if current > 1 {
            s := s + current;
        }
        
        if s == t {
            assume 1 <= t <= 1000000000;
            return t;
        }
        current := s;
        assume current >= 1;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 10000
    decreases *
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    while t > 0
        invariant t >= 0
        invariant a >= 0
        invariant b >= 0
        invariant k >= 0
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
        var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
        result := x + y;
        assume 1 <= result <= 10000;
        return;
    }
    
    if a == b {
        result := n;
        assume 1 <= result <= 10000;
        return;
    }
    
    assume n + 1 <= 1000000000;
    result := closestFair_2417(n + 1);
}

function power10(exp: int): int
    requires exp >= 0
    ensures power10(exp) >= 1
{
    if exp == 0 then 1
    else 10 * power10(exp - 1)
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 1000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant x >= 0
        invariant |stk| >= 1
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top * x];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            stk := stk[..|stk| - 1] + [top / x];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := sumArray(stk);
    assume 0 <= result <= 1000000;
}

function sumArray(arr: seq<int>): int
{
    if |arr| == 0 then 0
    else arr[0] + sumArray(arr[1..])
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result >= 1
    decreases *
{
    var x := n + 1;
    
    while true
        decreases *
    {
        var y := x;
        var cnt := new int[10];
        var i := 0;
        while i < 10
            invariant 0 <= i <= 10
        {
            cnt[i] := 0;
            i := i + 1;
        }
        
        while y > 0
            invariant y >= 0
            decreases y
        {
            var v := y % 10;
            y := y / 10;
            if 0 <= v < 10 {
                cnt[v] := cnt[v] + 1;
            }
        }
        
        var isBeautiful := true;
        i := 0;
        while i < 10 && isBeautiful
            invariant 0 <= i <= 10
        {
            if cnt[i] != 0 && i != cnt[i] {
                isBeautiful := false;
            }
            i := i + 1;
        }
        
        if isBeautiful {
            return x;
        }
        x := x + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures result >= 1
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := closestFair_2417(o1);
    var o3 := clumsy_1006(o2);
    var o4 := nextBeautifulNumber_2048(o3);
    result := o4;
}
