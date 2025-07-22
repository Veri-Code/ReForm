
method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 10000
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant 0 <= ans
        invariant 0 <= cnt
        invariant 0 <= num
        decreases num
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
    if result == 0 { result := 1; }
    if result > 10000 { result := 10000; }
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 0 <= result <= 1000000
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n
        invariant 0 <= k <= 3
        invariant |stk| >= 1
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
    
    var sum := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        decreases |stk| - i
    {
        sum := sum + stk[i];
        i := i + 1;
    }
    
    result := if sum < 0 then 0 else if sum > 1000000 then 1000000 else sum;
}

method getDigitCounts(x: int) returns (counts: array<int>)
    requires x > 0
    ensures counts.Length == 10
    ensures forall i :: 0 <= i < 10 ==> 0 <= counts[i]
{
    counts := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
        decreases 10 - i
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var num := x;
    while num > 0
        invariant 0 <= num
        invariant forall j :: 0 <= j < 10 ==> 0 <= counts[j]
        decreases num
    {
        var digit := num % 10;
        if 0 <= digit <= 9 {
            counts[digit] := counts[digit] + 1;
        }
        num := num / 10;
    }
}

method isBeautifulHelper(x: int) returns (beautiful: bool)
    requires x > 0
{
    var counts := getDigitCounts(x);
    
    beautiful := true;
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        decreases 10 - i
    {
        if counts[i] != 0 && counts[i] != i {
            beautiful := false;
            break;
        }
        i := i + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 2147483648
    ensures result > n
{
    var x := n + 1;
    
    while x <= 1224444
        invariant n < x <= 1224445
        decreases 1224445 - x
    {
        var isBeautiful := isBeautifulHelper(x);
        if isBeautiful {
            result := x;
            return;
        }
        x := x + 1;
    }
    
    result := 1224444;
}

method integerReplacement_397(n: int) returns (result: int)
    requires 1 <= n <= 2147483648
    ensures 1 <= result <= 1000
{
    var ans := 0;
    var num := n;
    
    while num != 1 && ans < 999
        invariant 1 <= num
        invariant 0 <= ans < 1000
        decreases if num == 1 then 0 else 2147483648 - ans
    {
        if num % 2 == 0 {
            num := num / 2;
        } else if num != 3 && num % 4 == 3 {
            num := num + 1;
        } else {
            num := num - 1;
        }
        ans := ans + 1;
    }
    
    if num == 1 {
        result := if ans == 0 then 1 else ans;
    } else {
        result := 1000;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 0 <= result
{
    var sum := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant 0 <= sum
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            sum := sum + x;
        }
        x := x + 1;
    }
    
    result := sum;
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 100000
    ensures 0 <= result
{
    var o1 := minOperations_2571(o);
    var o2 := clumsy_1006(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    var o4 := integerReplacement_397(o3);
    var o5 := sumOfMultiples_2652(o4);
    result := o5;
}
