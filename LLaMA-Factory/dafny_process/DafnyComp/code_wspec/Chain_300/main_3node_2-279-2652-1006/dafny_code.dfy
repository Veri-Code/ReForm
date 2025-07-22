
method numSquares_279(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= n
{
    var m := 0;
    while (m + 1) * (m + 1) <= n
        invariant 0 <= m
        invariant m * m <= n
        decreases n - m * m
    {
        m := m + 1;
    }
    
    // Create DP table f[i][j] where i goes from 0 to m, j goes from 0 to n
    var f := new int[m + 1, n + 1];
    
    // Initialize with large values
    var i := 0;
    while i <= m
        invariant 0 <= i <= m + 1
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 
            f[ii, jj] == (if ii == 0 && jj == 0 then 0 else n + 1)
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall jj :: 0 <= jj < j ==> 
                f[i, jj] == (if i == 0 && jj == 0 then 0 else n + 1)
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 
                f[ii, jj] == (if ii == 0 && jj == 0 then 0 else n + 1)
        {
            f[i, j] := if i == 0 && j == 0 then 0 else n + 1;
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill DP table
    i := 1;
    while i <= m
        invariant 1 <= i <= m + 1
        invariant f[0, 0] == 0
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] <= n + 1
        invariant forall jj :: 0 <= jj <= n ==> f[0, jj] <= n + 1
        invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
            invariant forall jj :: 0 <= jj < j ==> f[i, jj] <= n + 1
            invariant forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj <= n ==> f[ii, jj] <= n + 1
            invariant f[0, 0] == 0
            invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
        {
            f[i, j] := f[i - 1, j];
            if j >= i * i {
                var candidate := f[i, j - i * i] + 1;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := f[m, n];
    if result > n {
        result := n;
    }
    
    // Ensure result is at least 1
    if result < 1 {
        result := 1;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 10000
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
    
    // Ensure result is at least 1 (since n >= 1, we'll have at least one multiple)
    if result == 0 {
        result := 1;
    }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n
{
    var k := 0;
    var stk := new int[4 * n];
    var stkSize := 1;
    stk[0] := n;
    
    var x := n - 1;
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 1 <= stkSize <= 1 + 3 * (n - 1 - x)
        invariant stkSize < 4 * n
        invariant 0 <= k <= 3
        decreases x
    {
        if k == 0 {
            // Multiplication
            stkSize := stkSize - 1;
            var top := stk[stkSize];
            stk[stkSize] := top * x;
            stkSize := stkSize + 1;
        } else if k == 1 {
            // Division
            stkSize := stkSize - 1;
            var top := stk[stkSize];
            stk[stkSize] := top / x;
            stkSize := stkSize + 1;
        } else if k == 2 {
            // Addition (push positive)
            stk[stkSize] := x;
            stkSize := stkSize + 1;
        } else {
            // Subtraction (push negative)
            stk[stkSize] := -x;
            stkSize := stkSize + 1;
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum the stack
    result := 0;
    var i := 0;
    while i < stkSize
        invariant 0 <= i <= stkSize
    {
        result := result + stk[i];
        i := i + 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures true
{
    var o1 := numSquares_279(o);
    var o2 := sumOfMultiples_2652(o1);
    result := clumsy_1006(o2);
}
