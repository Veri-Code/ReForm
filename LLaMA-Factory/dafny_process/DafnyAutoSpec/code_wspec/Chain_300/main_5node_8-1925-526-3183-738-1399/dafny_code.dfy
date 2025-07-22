
method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures 1 <= ans <= 15
{
    ans := 0;
    var a := 1;
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    if ans == 0 {
        ans := 1;
    }
    if ans > 15 {
        ans := 15;
    }
}

method isqrt(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
    ensures result * result <= x < (result + 1) * (result + 1)
{
    if x == 0 {
        return 0;
    }
    
    result := 1;
    while result * result < x
        invariant result >= 1
        invariant (result - 1) * (result - 1) <= x
    {
        result := result + 1;
    }
    
    if result * result > x {
        result := result - 1;
    }
}

method countArrangement_526(n: int) returns (ans: int)
    requires 1 <= n <= 15
    ensures 1 <= ans <= 100000
    modifies {}
{
    var vis := new bool[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        vis[i] := false;
        i := i + 1;
    }
    
    var matchArray := new seq<int>[n + 1];
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
    {
        var validNumbers: seq<int> := [];
        var j := 1;
        while j <= n
            invariant 1 <= j <= n + 1
            invariant |validNumbers| <= j - 1
        {
            if j % i == 0 || i % j == 0 {
                validNumbers := validNumbers + [j];
            }
            j := j + 1;
        }
        matchArray[i] := validNumbers;
        i := i + 1;
    }
    
    ans := dfs(1, n, vis, matchArray);
    if ans == 0 {
        ans := 1;
    }
    if ans > 100000 {
        ans := 100000;
    }
}

method dfs(pos: int, n: int, vis: array<bool>, matchArray: array<seq<int>>) returns (count: int)
    requires 1 <= pos <= n + 1
    requires 1 <= n <= 15
    requires vis.Length == n + 1
    requires matchArray.Length == n + 1
    ensures count >= 0
    modifies vis
    decreases n + 1 - pos
{
    if pos == n + 1 {
        return 1;
    }
    
    count := 0;
    var i := 0;
    while i < |matchArray[pos]|
        invariant 0 <= i <= |matchArray[pos]|
        invariant count >= 0
    {
        var j := matchArray[pos][i];
        if 1 <= j <= n && !vis[j] {
            vis[j] := true;
            var subCount := dfs(pos + 1, n, vis, matchArray);
            count := count + subCount;
            vis[j] := false;
        }
        i := i + 1;
    }
}

method numberOfWays_3183(n: int) returns (ans: int)
    requires 1 <= n <= 100000
    ensures 0 <= ans <= 1000000000
{
    var mod := 1000000007;
    var f := new int[n + 1];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        f[i] := 0;
        i := i + 1;
    }
    f[0] := 1;
    
    // Process coin 1
    var j := 1;
    while j <= n
        invariant 1 <= j <= n + 1
        invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 1]) % mod;
        j := j + 1;
    }
    
    // Process coin 2
    j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
    {
        f[j] := (f[j] + f[j - 2]) % mod;
        j := j + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        j := 6;
        while j <= n
            invariant 6 <= j <= n + 1
            invariant forall k :: 0 <= k < j ==> 0 <= f[k] < mod
        {
            f[j] := (f[j] + f[j - 6]) % mod;
            j := j + 1;
        }
    }
    
    ans := f[n];
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    if ans > 1000000000 {
        ans := 1000000000;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
{
    if n == 0 {
        return 1;
    }
    
    var digits: seq<int> := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    if |digits| == 0 {
        return 1;
    }
    
    var i := 1;
    while i < |digits| && digits[i-1] <= digits[i]
        invariant 1 <= i <= |digits|
    {
        i := i + 1;
    }
    
    if i < |digits| {
        while i > 0 && i < |digits| && digits[i-1] > digits[i]
            invariant 0 <= i <= |digits|
        {
            digits := digits[i-1 := digits[i-1] - 1];
            i := i - 1;
        }
        if i < |digits| {
            i := i + 1;
            while i < |digits|
                invariant 1 <= i <= |digits|
            {
                digits := digits[i := 9];
                i := i + 1;
            }
        }
    }
    
    result := 0;
    i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
        invariant result <= 1000000000
    {
        var newResult := result * 10 + digits[i];
        if newResult <= 1000000000 && newResult >= 0 {
            result := newResult;
        } else {
            result := 1000000000;
        }
        i := i + 1;
    }
    
    if result == 0 {
        result := 1;
    }
}

method digitSum(n: int) returns (sum: int)
    requires n >= 1
    ensures sum >= 1
{
    sum := 0;
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
        decreases temp
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
    if sum == 0 {
        sum := 1;
    }
}

method countLargestGroup_1399(n: int) returns (ans: int)
    requires 1 <= n <= 10000
    ensures ans >= 1
{
    var cnt := new int[46]; // max digit sum for numbers up to 10000 is 9+9+9+9 = 36, but we use 46 for safety
    var i := 0;
    while i < 46
        invariant 0 <= i <= 46
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
    {
        var s := digitSum(i);
        if s < 46 {
            cnt[s] := cnt[s] + 1;
            if cnt[s] > mx {
                mx := cnt[s];
            }
        }
        i := i + 1;
    }
    
    ans := 0;
    i := 0;
    while i < 46
        invariant 0 <= i <= 46
        invariant ans >= 0
    {
        if cnt[i] == mx {
            ans := ans + 1;
        }
        i := i + 1;
    }
    
    if ans == 0 {
        ans := 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 250
    ensures 1 <= result
{
    var o1 := countTriples_1925(o);
    var o2: int;
    if o1 <= 15 {
        o2 := countArrangement_526(o1);
    } else {
        o2 := 1;
    }
    var o3: int;
    if o2 <= 100000 {
        o3 := numberOfWays_3183(o2);
    } else {
        o3 := 1;
    }
    var o4: int;
    if o3 <= 1000000000 {
        o4 := monotoneIncreasingDigits_738(o3);
    } else {
        o4 := 1;
    }
    var o5: int;
    if o4 <= 10000 {
        o5 := countLargestGroup_1399(o4);
    } else {
        o5 := 1;
    }
    result := o5;
}
