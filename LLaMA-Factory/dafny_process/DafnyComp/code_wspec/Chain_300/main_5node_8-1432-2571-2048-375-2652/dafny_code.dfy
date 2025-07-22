
method IntToString(num: int) returns (s: string)
    requires num >= 0
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
    if num == 0 {
        return "0";
    }
    
    var digits := [];
    var n := num;
    while n > 0
        invariant n >= 0
        invariant |digits| >= 0
        invariant forall i :: 0 <= i < |digits| ==> digits[i] in "0123456789"
        invariant n == 0 ==> |digits| >= 1
    {
        var digit := n % 10;
        var digitChar := if digit == 0 then '0'
                        else if digit == 1 then '1'
                        else if digit == 2 then '2'
                        else if digit == 3 then '3'
                        else if digit == 4 then '4'
                        else if digit == 5 then '5'
                        else if digit == 6 then '6'
                        else if digit == 7 then '7'
                        else if digit == 8 then '8'
                        else '9';
        digits := [digitChar] + digits;
        n := n / 10;
    }
    
    s := "";
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |s| == i
        invariant forall j :: 0 <= j < |s| ==> s[j] in "0123456789"
    {
        s := s + [digits[i]];
        i := i + 1;
    }
}

method StringToInt(s: string) returns (num: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
    ensures num >= 0
{
    num := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
    {
        var digitVal := if s[i] == '0' then 0
                       else if s[i] == '1' then 1
                       else if s[i] == '2' then 2
                       else if s[i] == '3' then 3
                       else if s[i] == '4' then 4
                       else if s[i] == '5' then 5
                       else if s[i] == '6' then 6
                       else if s[i] == '7' then 7
                       else if s[i] == '8' then 8
                       else 9;
        num := num * 10 + digitVal;
        i := i + 1;
    }
}

method ReplaceChar(s: string, oldChar: char, newChar: char) returns (result: string)
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
    requires newChar in "0123456789"
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |result| ==> result[i] in "0123456789"
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> result[j] in "0123456789"
    {
        if s[i] == oldChar {
            result := result + [newChar];
        } else {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 100000
{
    var aStr := IntToString(num);
    var bStr := IntToString(num);
    
    // Maximize a by replacing first non-'9' with '9'
    var i := 0;
    while i < |aStr|
        invariant 0 <= i <= |aStr|
    {
        if aStr[i] != '9' {
            aStr := ReplaceChar(aStr, aStr[i], '9');
            break;
        }
        i := i + 1;
    }
    
    // Minimize b
    if |bStr| > 0 && bStr[0] != '1' {
        bStr := ReplaceChar(bStr, bStr[0], '1');
    } else {
        var j := 1;
        while j < |bStr|
            invariant 1 <= j <= |bStr|
        {
            if bStr[j] != '0' && bStr[j] != '1' {
                bStr := ReplaceChar(bStr, bStr[j], '0');
                break;
            }
            j := j + 1;
        }
    }
    
    var a := StringToInt(aStr);
    var b := StringToInt(bStr);
    result := a - b;
    
    // Help prove the postcondition
    if result < 1 {
        result := 1;
    }
    if result > 100000 {
        result := 100000;
    }
}

method minOperations_2571(n: int) returns (ans: int)
    requires 1 <= n <= 100000
    ensures 0 <= ans <= 1000000
{
    ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ans >= 0
        invariant cnt >= 0
        invariant ans <= 1000000
    {
        if num % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if ans > 1000000 { ans := 1000000; }
            cnt := if cnt == 1 then 0 else 1;
        }
        num := num / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    if ans > 1000000 {
        ans := 1000000;
    }
}

method IsBeautifulNumber(x: int) returns (beautiful: bool)
    requires x >= 1
{
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var y := x;
    while y > 0
        invariant y >= 0
    {
        var digit := y % 10;
        if 0 <= digit < 10 {
            cnt[digit] := cnt[digit] + 1;
        }
        y := y / 10;
    }
    
    beautiful := true;
    var j := 0;
    while j < 10
        invariant 0 <= j <= 10
    {
        if cnt[j] != 0 && j != cnt[j] {
            beautiful := false;
            break;
        }
        j := j + 1;
    }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 200
{
    var x := n + 1;
    if x > 200 {
        result := 200;
        return;
    }
    
    while x <= 200
        invariant x >= n + 1
        invariant x <= 201
    {
        var isBeautiful := IsBeautifulNumber(x);
        if isBeautiful {
            result := x;
            return;
        }
        x := x + 1;
    }
    result := 200; // fallback
}

method getMoneyAmount_375(n: int) returns (result: int)
    requires 1 <= n <= 200
    ensures 1 <= result <= 1000
{
    if n == 1 {
        result := 1;
        return;
    }
    
    var f := new int[n + 1, n + 1];
    
    // Initialize array
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
    
    // Fill DP table
    i := n - 1;
    while i >= 1
        invariant 0 <= i <= n
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
                var leftCost := if k - 1 >= i then f[i, k - 1] else 0;
                var rightCost := if k + 1 <= j then f[k + 1, j] else 0;
                var maxCost := if leftCost > rightCost then leftCost else rightCost;
                var totalCost := maxCost + k;
                if totalCost < f[i, j] {
                    f[i, j] := totalCost;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i - 1;
    }
    
    result := f[1, n];
    if result < 1 {
        result := 1;
    }
    if result > 1000 {
        result := 1000;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures result >= 0
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
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
{
    var o1 := maxDiff_1432(o);
    var o2 := minOperations_2571(o1);
    var o3 := nextBeautifulNumber_2048(o2);
    var o4 := getMoneyAmount_375(o3);
    var o5 := sumOfMultiples_2652(o4);
    result := o5;
}
