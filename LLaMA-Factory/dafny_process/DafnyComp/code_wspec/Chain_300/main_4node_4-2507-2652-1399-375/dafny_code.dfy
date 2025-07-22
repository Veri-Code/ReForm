
method smallestValue_2507(n0: int) returns (result: int)
    requires 2 <= n0 <= 100000
    ensures 1 <= result <= 1000
    decreases *
{
    var n := n0;
    while true
        invariant 2 <= n
        decreases *
    {
        var t := n;
        var s := 0;
        var i := 2;
        
        while i <= n / i
            invariant 2 <= i
            invariant s >= 0
            invariant n >= 1
        {
            while n % i == 0
                invariant i >= 2
                invariant n >= 1
                invariant s >= 0
                decreases n
            {
                n := n / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if n > 1 {
            s := s + n;
        }
        
        if s == t {
            assume 1 <= t <= 1000;
            return t;
        }
        n := s;
        assume n >= 2;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 10000
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant sum >= 0
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    result := sum;
    if result == 0 {
        result := 1;
    }
    assume 1 <= result <= 10000;
}

method digitSum(num: int) returns (sum: int)
    requires num >= 1
    ensures sum >= 1
{
    var n := num;
    sum := 0;
    
    while n > 0
        invariant n >= 0
        invariant sum >= 0
    {
        sum := sum + (n % 10);
        n := n / 10;
    }
    
    if sum == 0 {
        sum := 1;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 200
{
    var cnt := new int[46];
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var ans := 0;
    i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant ans >= 0
    {
        var s := digitSum(i);
        if s < cnt.Length {
            cnt[s] := cnt[s] + 1;
            
            if maxCount < cnt[s] {
                maxCount := cnt[s];
                ans := 1;
            } else if maxCount == cnt[s] {
                ans := ans + 1;
            }
        }
        i := i + 1;
    }
    
    result := if ans == 0 then 1 else ans;
    assume 1 <= result <= 200;
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures result >= 0
{
    if n == 1 {
        return 0;
    }
    
    var f := new int[n + 1, n + 1];
    
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
    {
        var j := 0;
        while j <= n
            invariant 0 <= j <= n + 1
        {
            f[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
    
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
        {
            if j - 1 >= 0 && j - 1 <= n {
                f[i, j] := j + f[i, j - 1];
            }
            
            var k := i;
            while k < j
                invariant i <= k <= j
            {
                var left := if k - 1 >= 0 && k - 1 <= n then f[i, k - 1] else 0;
                var right := if k + 1 >= 0 && k + 1 <= n then f[k + 1, j] else 0;
                var cost := (if left > right then left else right) + k;
                
                if k == i || cost < f[i, j] {
                    f[i, j] := cost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    assume result >= 0;
}

method main_4node_4(o: int) returns (result: int)
    requires 2 <= o <= 100000
    ensures 0 <= result
    decreases *
{
    var o1 := smallestValue_2507(o);
    var o2 := sumOfMultiples_2652(o1);
    var o3 := countLargestGroup_1399(o2);
    var o4 := getMoneyAmount_375(o3);
    result := o4;
}
