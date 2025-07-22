
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 10000
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 < a <= mx || a == mx / 10
        invariant mx == power10(n) - 1
        decreases a
    {
        var b := a;
        var x := a;
        
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            invariant mx == power10(n) - 1
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 {
                    return 1337;
                }
                return res;
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    return 9;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 100000
{
    var cnt := new int[100]; // digit sums can be at most 9*5 = 45 for n <= 10000
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var ans := 0;
    var mx := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
        invariant ans <= i - 1
        decreases n - i
    {
        var temp := i;
        var s := 0;
        
        while temp > 0
            invariant temp >= 0
            invariant s >= 0
            decreases temp
        {
            s := s + temp % 10;
            temp := temp / 10;
        }
        
        if s < cnt.Length {
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
    
    return if ans == 0 then 1 else ans;
}

method numberOfWays_3183(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 100000
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
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant f[0] == 1
        invariant forall j :: 0 <= j < i ==> f[j] >= 0
    {
        f[i] := (f[i] + f[i - 1]) % mod;
        i := i + 1;
    }
    
    // Process coin 2
    i := 2;
    while i <= n
        invariant 2 <= i <= n + 1
        invariant forall j :: 0 <= j < i ==> f[j] >= 0
    {
        f[i] := (f[i] + f[i - 2]) % mod;
        i := i + 1;
    }
    
    // Process coin 6
    if n >= 6 {
        i := 6;
        while i <= n
            invariant 6 <= i <= n + 1
            invariant forall j :: 0 <= j < i ==> f[j] >= 0
        {
            f[i] := (f[i] + f[i - 6]) % mod;
            i := i + 1;
        }
    }
    
    var ans := f[n];
    
    if n >= 4 {
        ans := (ans + f[n - 4]) % mod;
    }
    
    if n >= 8 {
        ans := (ans + f[n - 8]) % mod;
    }
    
    if ans == 0 {
        return 1;
    } else if ans > 100000 {
        return 100000;
    } else {
        return ans;
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires n >= 1
    ensures result >= 0
{
    var ans := 0;
    var cnt := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant ans >= 0
        invariant cnt >= 0
        decreases temp
    {
        if temp % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        temp := temp / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    return ans;
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) >= 1
    ensures n >= 1 ==> power10(n) >= 10
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else 100000000
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 0
{
    var o1 := largestPalindrome_479(o);
    var o2 := countLargestGroup_1399(o1);
    var o3 := numberOfWays_3183(o2);
    var o4 := minOperations_2571(o3);
    return o4;
}
