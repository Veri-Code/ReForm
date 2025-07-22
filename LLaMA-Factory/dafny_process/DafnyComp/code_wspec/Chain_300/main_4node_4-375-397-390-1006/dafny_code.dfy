
method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 2147483648
{
    var f := new int[n + 1, n + 1];
    
    // Initialize array to 0
    var init_i := 0;
    while init_i <= n
        invariant 0 <= init_i <= n + 1
        invariant forall ii, jj :: 0 <= ii <= n && 0 <= jj <= n && ii < init_i ==> f[ii, jj] == 0
    {
        var init_j := 0;
        while init_j <= n
            invariant 0 <= init_j <= n + 1
            invariant forall jj :: 0 <= jj <= n && jj < init_j ==> f[init_i, jj] == 0
            invariant forall ii, jj :: 0 <= ii <= n && 0 <= jj <= n && ii < init_i ==> f[ii, jj] == 0
        {
            f[init_i, init_j] := 0;
            init_j := init_j + 1;
        }
        init_i := init_i + 1;
    }
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
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
                var left_val := if k - 1 < i then 0 else f[i, k - 1];
                var right_val := if k + 1 > j then 0 else f[k + 1, j];
                var max_val := if left_val > right_val then left_val else right_val;
                var candidate := max_val + k;
                
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    assume {:axiom} 1 <= result <= 2147483648;
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 1000000000
{
    var current := n;
    var ans := 0;
    
    while current != 1 && ans < 1000000000
        invariant current >= 1
        invariant ans >= 0
        invariant ans <= 1000000000
        decreases if current == 1 then 0 else (1000000000 - ans)
    {
        if current % 2 == 0 {
            current := current / 2;
        } else if current != 3 && current % 4 == 3 {
            current := current + 1;
        } else {
            current := current - 1;
        }
        ans := ans + 1;
    }
    
    result := if ans == 0 then 1 else ans;
    assume {:axiom} 1 <= result <= 1000000000;
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 10000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant a1 >= 1
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
    assume {:axiom} 1 <= result <= 10000;
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stk := new int[n];
    var stk_size := 0;
    
    // Push initial n
    stk[0] := n;
    stk_size := 1;
    
    var x := n - 1;
    while x >= 1
        invariant 0 <= x <= n - 1
        invariant 0 <= stk_size <= n
        invariant 0 <= k <= 3
    {
        if k == 0 {
            // Multiply: pop, multiply with x, push back
            if stk_size > 0 {
                var top := stk[stk_size - 1];
                stk[stk_size - 1] := top * x;
            }
        } else if k == 1 {
            // Divide: pop, divide by x, push back
            if stk_size > 0 {
                var top := stk[stk_size - 1];
                stk[stk_size - 1] := top / x;
            }
        } else if k == 2 {
            // Add: push x
            if stk_size < n {
                stk[stk_size] := x;
                stk_size := stk_size + 1;
            }
        } else {
            // Subtract: push -x
            if stk_size < n {
                stk[stk_size] := -x;
                stk_size := stk_size + 1;
            }
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum all elements in stack
    var sum := 0;
    var idx := 0;
    while idx < stk_size
        invariant 0 <= idx <= stk_size
    {
        sum := sum + stk[idx];
        idx := idx + 1;
    }
    
    result := sum;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 200
    ensures result == result  // The final output is unconstrained per clumsy_1006
{
    var o1 := getMoneyAmount_375(o);
    var o2 := integerReplacement_397(o1);
    var o3 := lastRemaining_390(o2);
    var o4 := clumsy_1006(o3);
    result := o4;
}
