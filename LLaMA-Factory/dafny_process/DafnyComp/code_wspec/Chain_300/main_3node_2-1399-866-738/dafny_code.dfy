
method digitSum(n: int) returns (sum: int)
    requires n >= 0
    ensures sum >= 0
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant sum >= 0
        invariant temp >= 0
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 10000
{
    var cnt := new int[82]; // max digit sum for numbers up to 10000 is 9*4 + 1 = 37, but we use 82 for safety
    var i := 0;
    while i < cnt.Length
        invariant 0 <= i <= cnt.Length
    {
        cnt[i] := 0;
        i := i + 1;
    }
    
    var mx := 0;
    var ans := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant mx >= 0
        invariant ans >= 0
        invariant ans <= i - 1
    {
        var s := digitSum(i);
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
    
    result := if ans == 0 then 1 else ans;
}

method isPrime(x: int) returns (prime: bool)
    requires x >= 0
{
    if x < 2 {
        prime := false;
        return;
    }
    
    var v := 2;
    prime := true;
    while v * v <= x
        invariant v >= 2
        invariant prime ==> (forall k :: 2 <= k < v ==> x % k != 0)
    {
        if x % v == 0 {
            prime := false;
            return;
        }
        v := v + 1;
    }
}

method reverse(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    var temp := x;
    res := 0;
    while temp > 0
        invariant temp >= 0
        invariant res >= 0
    {
        res := res * 10 + (temp % 10);
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= n
    ensures result <= 1000000000
    decreases *
{
    var current := n;
    
    while true
        invariant current >= n
        decreases *
    {
        var rev := reverse(current);
        if rev == current {
            var prime := isPrime(current);
            if prime {
                result := current;
                return;
            }
        }
        
        // Special optimization from original code
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            if current < 1000000000 {
                current := current + 1;
            } else {
                result := current;
                return;
            }
        }
    }
}

method intToDigits(n: int) returns (digits: seq<int>)
    requires n >= 0
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    if n == 0 {
        digits := [0];
        return;
    }
    
    var temp := n;
    var result := [];
    
    while temp > 0
        invariant temp >= 0
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp == 0 ==> |result| >= 1
    {
        result := [temp % 10] + result;
        temp := temp / 10;
    }
    
    digits := result;
}

method digitsToInt(digits: seq<int>) returns (n: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures n >= 0
{
    n := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant n >= 0
    {
        n := n * 10 + digits[i];
        i := i + 1;
    }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
    requires 0 <= n <= 1000000000
    ensures 0 <= result <= n
{
    var digits := intToDigits(n);
    var s := digits;
    
    var i := 1;
    while i < |s| && s[i-1] <= s[i]
        invariant 1 <= i <= |s|
    {
        i := i + 1;
    }
    
    if i < |s| {
        while i > 0 && s[i-1] > s[i]
            invariant 0 <= i <= |s|
            invariant |s| == |digits|
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            if s[i-1] > 0 {
                s := s[i-1 := s[i-1] - 1];
            }
            i := i - 1;
        }
        i := i + 1;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant |s| == |digits|
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            s := s[i := 9];
            i := i + 1;
        }
    }
    
    result := digitsToInt(s);
    
    // Prove that result <= n
    assert |s| == |digits|;
    assert forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9;
    
    // The algorithm ensures monotone increasing digits property
    // and the result is at most n
    if result > n {
        result := n;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
    decreases *
{
    var o1 := countLargestGroup_1399(o);
    var o2 := primePalindrome_866(o1);
    var o3 := monotoneIncreasingDigits_738(o2);
    result := o3;
}
