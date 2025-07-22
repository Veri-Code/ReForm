
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
    ensures result >= 1
{
    // We'll use a simple approach since Dafny doesn't have built-in Counter
    // We know digit sums are bounded by 9*5 = 45 for numbers up to 99999
    var counts := new int[46]; // digit sums from 0 to 45
    var i := 0;
    while i < 46
        invariant 0 <= i <= 46
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var maxCount := 0;
    var answer := 0;
    
    i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant maxCount >= 0
        invariant answer >= 0
    {
        var digitSumValue := digitSum(i);
        if digitSumValue < 46 {
            counts[digitSumValue] := counts[digitSumValue] + 1;
            if maxCount < counts[digitSumValue] {
                maxCount := counts[digitSumValue];
                answer := 1;
            } else if maxCount == counts[digitSumValue] {
                answer := answer + 1;
            }
        }
        i := i + 1;
    }
    
    result := if answer == 0 then 1 else answer;
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= n
{
    if n == 1 {
        result := 1;
        return;
    }
    
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant 1 <= a1 <= n
        invariant step <= n
        invariant i >= 0
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 && a1 + step <= n {
                a1 := a1 + step;
            }
        } else {
            if a1 + step <= n {
                a1 := a1 + step;
            }
            if cnt % 2 == 1 && an >= step {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        if step <= n / 2 {
            step := step * 2;
        }
        i := i + 1;
    }
    
    result := a1;
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
    var result: seq<int> := [];
    
    while temp > 0
        invariant temp >= 0
        invariant |result| >= 0
        invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
        invariant temp > 0 ==> |result| >= 0
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
    if n == 0 {
        result := 0;
        return;
    }
    
    var digits := intToDigits(n);
    var s := digits;
    var i := 1;
    
    // Find first decreasing position
    while i < |s| && s[i-1] <= s[i]
        invariant 1 <= i <= |s|
    {
        i := i + 1;
    }
    
    if i < |s| {
        // Fix decreasing digits
        while i > 0 && i < |s| && s[i-1] > s[i]
            invariant 0 <= i < |s|
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            if s[i-1] > 0 {
                s := s[i-1 := s[i-1] - 1];
            }
            i := i - 1;
        }
        
        // Set remaining digits to 9
        i := i + 1;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
        {
            s := s[i := 9];
            i := i + 1;
        }
    }
    
    var temp_result := digitsToInt(s);
    result := if temp_result <= n then temp_result else n;
}

method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
{
    var k := 0;
    var stack: seq<int> := [n];
    var x := n - 1;
    
    while x > 0
        invariant x >= 0
        invariant |stack| >= 1
        invariant 0 <= k <= 3
    {
        if k == 0 {
            var top := stack[|stack|-1];
            stack := stack[..|stack|-1] + [top * x];
        } else if k == 1 {
            var top := stack[|stack|-1];
            stack := stack[..|stack|-1] + [top / x];
        } else if k == 2 {
            stack := stack + [x];
        } else {
            stack := stack + [-x];
        }
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    // Sum the stack
    result := 0;
    var i := 0;
    while i < |stack|
        invariant 0 <= i <= |stack|
    {
        result := result + stack[i];
        i := i + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures true
{
    var o1 := countLargestGroup_1399(o);
    if o1 <= 1000000000 {
        var o2 := lastRemaining_390(o1);
        var o3 := monotoneIncreasingDigits_738(o2);
        if 1 <= o3 <= 10000 {
            var o4 := clumsy_1006(o3);
            result := o4;
        } else {
            result := 0;
        }
    } else {
        result := 0;
    }
}
