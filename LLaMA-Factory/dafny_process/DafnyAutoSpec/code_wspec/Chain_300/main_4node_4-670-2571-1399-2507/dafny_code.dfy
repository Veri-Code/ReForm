
method DigitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant temp >= 0
        invariant sum >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method maximumSwap_670(num: int) returns (result: int)
    requires 0 <= num <= 100000000
    ensures result >= 0
{
    // Convert number to string representation (as array of digits)
    var digits: seq<int> := [];
    var temp := num;
    
    if temp == 0 {
        result := 0;
        return;
    }
    
    // Extract digits
    while temp > 0
        invariant temp >= 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        digits := [temp % 10] + digits;
        temp := temp / 10;
    }
    
    var n := |digits|;
    if n <= 1 {
        result := num;
        return;
    }
    
    // Create array d to track rightmost position of largest digit to the right
    var d: seq<int> := [];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |d| == i
        invariant forall k :: 0 <= k < i ==> 0 <= d[k] < n
    {
        d := d + [i];
        i := i + 1;
    }
    
    // Fill d array from right to left
    i := n - 2;
    while i >= 0
        invariant -1 <= i < n
        invariant |d| == n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        if digits[i] <= digits[d[i + 1]] {
            d := d[i := d[i + 1]];
        }
        i := i - 1;
    }
    
    // Find first position where we can make a beneficial swap
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |digits| == n
        invariant |d| == n
        invariant forall k :: 0 <= k < n ==> 0 <= d[k] < n
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        if digits[i] < digits[d[i]] {
            // Perform swap
            var temp_digit := digits[i];
            digits := digits[i := digits[d[i]]];
            digits := digits[d[i] := temp_digit];
            break;
        }
        i := i + 1;
    }
    
    // Convert back to integer
    result := 0;
    i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant result >= 0
        invariant forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
    {
        result := result * 10 + digits[i];
        i := i + 1;
    }
}

method minOperations_2571(n: int) returns (ans: int)
    requires 1 <= n
    ensures ans >= 0
{
    ans := 0;
    var cnt := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant ans >= 0
        invariant cnt >= 0
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
}

method countLargestGroup_1399(n: int) returns (ans: int)
    requires 1 <= n
    ensures ans >= 1
{
    // Use a map to count occurrences of each digit sum
    var cnt: map<int, int> := map[];
    ans := 1;
    var mx := 0;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ans >= 1
        invariant mx >= 0
    {
        var s := DigitSum(i);
        
        if s in cnt {
            cnt := cnt[s := cnt[s] + 1];
        } else {
            cnt := cnt[s := 1];
        }
        
        if mx < cnt[s] {
            mx := cnt[s];
            ans := 1;
        } else if mx == cnt[s] {
            ans := ans + 1;
        }
        
        i := i + 1;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n
    ensures result >= 2
    decreases *
{
    var current := n;
    
    while true
        invariant current >= 2
        decreases *
    {
        var t := current;
        var s := 0;
        var i := 2;
        var temp_current := current;
        
        // Factor the number and sum the prime factors
        while i <= temp_current / i
            invariant i >= 2
            invariant s >= 0
            invariant temp_current >= 1
        {
            while temp_current % i == 0
                invariant temp_current >= 1
                invariant i >= 2
                invariant s >= 0
                decreases temp_current
            {
                temp_current := temp_current / i;
                s := s + i;
            }
            i := i + 1;
        }
        
        if temp_current > 1 {
            s := s + temp_current;
        }
        
        if s == t {
            result := t;
            return;
        }
        
        if s < 2 {
            result := 2;
            return;
        }
        
        current := s;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 0 <= o <= 100000000
    ensures result >= 2
    decreases *
{
    var o1 := maximumSwap_670(o);
    
    var o2: int;
    if o1 >= 1 {
        o2 := minOperations_2571(o1);
    } else {
        o2 := minOperations_2571(1);
    }
    
    var o3: int;
    if o2 >= 1 {
        o3 := countLargestGroup_1399(o2);
    } else {
        o3 := countLargestGroup_1399(1);
    }
    
    if o3 >= 2 {
        result := smallestValue_2507(o3);
    } else {
        result := smallestValue_2507(2);
    }
}
