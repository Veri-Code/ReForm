
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        decreases x
    {
        if k == 0 {
            var top := stk[|stk| - 1];
            var new_val := top * x;
            stk := stk[..|stk| - 1] + [new_val];
        } else if k == 1 {
            var top := stk[|stk| - 1];
            var new_val := top / x;
            stk := stk[..|stk| - 1] + [new_val];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := sum_seq(stk);
    if result < 1 {
        result := 1;
    } else if result > 1000000000 {
        result := 1000000000;
    }
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 200
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
        invariant an >= 1
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if an < 1 {
                an := 1;
            }
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                if an >= step {
                    an := an - step;
                }
                if an < 1 {
                    an := 1;
                }
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result > 200 {
        result := 200;
    }
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures result >= 0
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var row := 0;
    while row <= n
        invariant 0 <= row <= n + 1
        invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] == 0
    {
        var col := 0;
        while col <= n
            invariant 0 <= col <= n + 1
            invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] == 0
            invariant forall c :: 0 <= c < col ==> f[row, c] == 0
        {
            f[row, col] := 0;
            col := col + 1;
        }
        row := row + 1;
    }
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
        invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
        decreases i
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
        {
            if j - 1 >= 0 && j - 1 <= n {
                f[i, j] := j + f[i, j - 1];
            } else {
                f[i, j] := j;
            }
            
            var k := i;
            while k < j
                invariant i <= k <= j
                invariant f[i, j] >= 0
                invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
            {
                var left_val := if k - 1 >= i && k - 1 >= 0 then f[i, k - 1] else 0;
                var right_val := if k + 1 <= j && k + 1 <= n then f[k + 1, j] else 0;
                var max_val := if left_val > right_val then left_val else right_val;
                var candidate := max_val + k;
                
                if candidate >= 0 && candidate < f[i, j] {
                    f[i, j] := candidate;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures true
{
    var o1 := clumsy_1006(o);
    var o2 := lastRemaining_390(o1);
    var o3 := getMoneyAmount_375(o2);
    result := o3;
}
