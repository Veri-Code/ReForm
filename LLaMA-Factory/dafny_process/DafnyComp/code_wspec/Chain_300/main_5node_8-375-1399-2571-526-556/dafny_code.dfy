
method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 10000
{
    var f := new int[n + 1, n + 1];
    
    var i := n - 1;
    while i >= 1
        invariant 0 <= i <= n - 1
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
        {
            f[i, j] := j + (if j == 0 then 0 else f[i, j - 1]);
            
            var k := i;
            while k < j
                invariant i <= k <= j
            {
                var left := if k == 0 then 0 else f[i, k - 1];
                var right := if k + 1 > n then 0 else f[k + 1, j];
                var candidate := (if left > right then left else right) + k;
                if candidate < f[i, j] {
                    f[i, j] := candidate;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := if n == 1 then 1 else f[1, n];
    if result <= 0 { result := 1; }
    if result > 10000 { result := 10000; }
}

method digitSum(num: int) returns (sum: int)
    requires num >= 0
    ensures sum >= 0
{
    sum := 0;
    var n := num;
    while n > 0
        invariant n >= 0
        invariant sum >= 0
        decreases n
    {
        sum := sum + (n % 10);
        n := n / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 100000
{
    var cnt := new int[100];
    var i := 0;
    while i < 100
        invariant 0 <= i <= 100
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 1;
    var mx := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 1
        invariant mx >= 0
    {
        var s := digitSum(i);
        if s < 100 {
            cnt[s] := cnt[s] + 1;
            if mx < cnt[s] {
                mx := cnt[s];
                ans := 1;
            } else if mx == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    result := ans;
    if result > 100000 { result := 100000; }
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 15
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases num
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            cnt := if cnt == 1 then 0 else 1;
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := if ans == 0 then 1 else ans;
    if result > 15 { result := 15; }
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 2147483648
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
        var matches: seq<int> := [];
        var j := 1;
        while j <= n
            invariant 1 <= j <= n + 1
        {
            if j % i == 0 || i % j == 0 {
                matches := matches + [j];
            }
            j := j + 1;
        }
        matchArray[i] := matches;
        i := i + 1;
    }
    
    var count := dfs_526(1, n, vis, matchArray);
    result := if count == 0 then 1 else count;
    if result > 2147483648 { result := 2147483648; }
}

method dfs_526(pos: int, n: int, vis: array<bool>, matchArray: array<seq<int>>) returns (count: int)
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
            var subCount := dfs_526(pos + 1, n, vis, matchArray);
            count := count + subCount;
            vis[j] := false;
        }
        i := i + 1;
    }
}

method intToString(num: int) returns (s: string)
    requires num >= 0
{
    if num == 0 {
        return "0";
    }
    
    var digits: seq<char> := [];
    var n := num;
    while n > 0
        invariant n >= 0
        decreases n
    {
        var digit := n % 10;
        var digitChar := (digit as char) + '0';
        digits := [digitChar] + digits;
        n := n / 10;
    }
    
    s := digits;
}

method stringToInt(s: string) returns (num: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures num >= 0
{
    num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
    {
        num := num * 10 + ((s[i] as int) - ('0' as int));
        i := i + 1;
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures result >= -1
{
    var s := intToString(n);
    if |s| == 0 {
        result := -1;
        return;
    }
    
    var cs: seq<char> := s;
    var len := |cs|;
    
    var i := len - 2;
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i < len - 1
        decreases i + 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        result := -1;
        return;
    }
    
    var j := len - 1;
    while j > i && cs[i] >= cs[j]
        invariant i < j < len
        decreases j - i
    {
        j := j - 1;
    }
    
    var temp := cs[i];
    cs := cs[i := cs[j]];
    cs := cs[j := temp];
    
    var left := i + 1;
    var right := len - 1;
    while left < right
        invariant i + 1 <= left <= right + 1 <= len
        invariant left <= len && right >= 0
        decreases right - left
    {
        if left < len && right >= 0 && left < |cs| && right < |cs| {
            temp := cs[left];
            cs := cs[left := cs[right]];
            cs := cs[right := temp];
        }
        left := left + 1;
        right := right - 1;
    }
    
    if |cs| > 0 && (forall k :: 0 <= k < |cs| ==> '0' <= cs[k] <= '9') {
        var ans := stringToInt(cs);
        result := if ans > 2147483647 then -1 else ans;
    } else {
        result := -1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 200
    ensures result >= -1
{
    var o1 := getMoneyAmount_375(o);
    var o2 := countLargestGroup_1399(o1);
    var o3 := minOperations_2571(o2);
    var o4 := countArrangement_526(o3);
    var o5 := nextGreaterElement_556(o4);
    result := o5;
}
