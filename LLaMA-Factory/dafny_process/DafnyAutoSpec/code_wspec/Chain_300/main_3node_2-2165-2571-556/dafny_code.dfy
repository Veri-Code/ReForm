
method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures if num >= 0 then result >= 0 else result <= 0
    ensures result != 0 || num == 0
{
    var neg := num < 0;
    var n := if num < 0 then -num else num;
    
    if n == 0 {
        return 0;
    }
    
    var cnt := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
        invariant forall k :: 0 <= k < i ==> cnt[k] == 0
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant cnt.Length == 10
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
        decreases temp
    {
        var digit := temp % 10;
        cnt[digit] := cnt[digit] + 1;
        temp := temp / 10;
    }
    
    var ans := 0;
    if neg {
        i := 9;
        while i >= 0
            invariant -1 <= i <= 9
            invariant cnt.Length == 10
            invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
            invariant ans >= 0
        {
            var j := 0;
            while j < cnt[i]
                invariant 0 <= j <= cnt[i]
                invariant cnt.Length == 10
                invariant cnt[i] >= 0
                invariant ans >= 0
            {
                ans := ans * 10 + i;
                j := j + 1;
            }
            i := i - 1;
        }
        if ans == 0 {
            return -1;
        }
        return -ans;
    }
    
    if cnt[0] > 0 {
        i := 1;
        while i < 10
            invariant 1 <= i <= 10
            invariant cnt.Length == 10
        {
            if cnt[i] > 0 {
                ans := i;
                cnt[i] := cnt[i] - 1;
                break;
            }
            i := i + 1;
        }
    }
    
    i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant cnt.Length == 10
        invariant ans >= 0
        invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
    {
        var j := 0;
        while j < cnt[i]
            invariant 0 <= j <= cnt[i]
            invariant cnt.Length == 10
            invariant cnt[i] >= 0
            invariant ans >= 0
        {
            ans := ans * 10 + i;
            j := j + 1;
        }
        i := i + 1;
    }
    
    if ans == 0 {
        ans := 1;
    }
    
    return ans;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures result >= 1
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
    
    if ans == 0 {
        ans := 1;
    }
    
    return ans;
}

method intToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        return "0";
    }
    
    var digits := [];
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant |digits| >= 0
        invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
        invariant temp > 0 ==> |digits| >= 0
        invariant n > 0 && temp == 0 ==> |digits| >= 1
        decreases temp
    {
        var digit := temp % 10;
        var digitChar := match digit
            case 0 => '0'
            case 1 => '1'
            case 2 => '2'
            case 3 => '3'
            case 4 => '4'
            case 5 => '5'
            case 6 => '6'
            case 7 => '7'
            case 8 => '8'
            case 9 => '9';
        digits := [digitChar] + digits;
        temp := temp / 10;
    }
    
    return digits;
}

method stringToInt(s: string) returns (n: int)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures n >= 0
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
    {
        var digitValue := s[i] as int - '0' as int;
        n := n * 10 + digitValue;
        i := i + 1;
    }
}

method nextGreaterElement_556(n: int) returns (result: int)
    requires 1 <= n <= 2147483647
    ensures result == -1 || result > n
{
    var s := intToString(n);
    var cs := s;
    var len := |cs|;
    
    if len <= 1 {
        return -1;
    }
    
    var i := len - 2;
    while i >= 0 && cs[i] >= cs[i + 1]
        invariant -1 <= i < len - 1
        decreases i + 1
    {
        i := i - 1;
    }
    
    if i < 0 {
        return -1;
    }
    
    var j := len - 1;
    while cs[i] >= cs[j]
        invariant i < j < len
        decreases j - i
    {
        j := j - 1;
    }
    
    // Swap cs[i] and cs[j]
    var temp := cs[i];
    cs := cs[i := cs[j]];
    cs := cs[j := temp];
    
    // Reverse cs[i+1..]
    var left := i + 1;
    var right := len - 1;
    while left < right
        invariant i + 1 <= left <= right + 1 <= len
        invariant 0 <= left < |cs|
        invariant 0 <= right < |cs|
        invariant forall k :: 0 <= k < |cs| ==> '0' <= cs[k] <= '9'
        decreases right - left
    {
        temp := cs[left];
        cs := cs[left := cs[right]];
        cs := cs[right := temp];
        left := left + 1;
        right := right - 1;
    }
    
    var ans := stringToInt(cs);
    if ans > 2147483647 || ans <= n {
        return -1;
    }
    return ans;
}

method main_3node_2(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result == -1 || result >= 1
{
    var o1 := smallestNumber_2165(o);
    
    if o1 <= 0 || o1 > 100000 {
        result := -1;
        return;
    }
    
    var o2 := minOperations_2571(o1);
    
    if o2 > 2147483647 {
        result := -1;
        return;
    }
    
    var o3 := nextGreaterElement_556(o2);
    result := o3;
}
