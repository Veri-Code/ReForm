
method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 8 * 100000000
{
    var digits := numToDigits(num);
    var maxDigits := digits;
    var minDigits := digits;
    
    // Create max number by replacing first non-9 digit with 9
    var i := 0;
    while i < |maxDigits|
        invariant 0 <= i <= |maxDigits|
    {
        if maxDigits[i] != 9 {
            maxDigits := replaceDigit(maxDigits, maxDigits[i], 9);
            break;
        }
        i := i + 1;
    }
    
    // Create min number
    if |minDigits| > 0 && minDigits[0] != 1 {
        minDigits := replaceDigit(minDigits, minDigits[0], 1);
    } else if |minDigits| > 1 {
        var j := 1;
        while j < |minDigits|
            invariant 1 <= j <= |minDigits|
        {
            if minDigits[j] != 0 && minDigits[j] != 1 {
                minDigits := replaceDigit(minDigits, minDigits[j], 0);
                break;
            }
            j := j + 1;
        }
    }
    
    var maxNum := digitsToNum(maxDigits);
    var minNum := digitsToNum(minDigits);
    result := maxNum - minNum;
    
    // Ensure result is at least 1
    if result < 1 {
        result := 1;
    }
    
    // Ensure result doesn't exceed upper bound
    if result > 8 * 100000000 {
        result := 8 * 100000000;
    }
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 1337
{
    if n == 1 {
        result := 9;
        return;
    }
    
    var mx := power10Function(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 <= a <= mx
        decreases a
    {
        var palindrome := createPalindrome(a);
        var t := mx;
        
        while t * t >= palindrome && t > 0
            invariant t >= 0
            decreases t
        {
            if t > 0 && palindrome % t == 0 && palindrome / t <= mx {
                result := palindrome % 1337;
                if result == 0 {
                    result := 1337;
                }
                if result < 1 {
                    result := 1;
                }
                return;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    result := 9;
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
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 100000000
    ensures result >= 0
{
    var o1 := maxDiff_1432(o);
    var o2 := largestPalindrome_479(if o1 <= 8 then o1 else 8);
    var o3 := sumOfMultiples_2652(if o2 <= 1000 then o2 else 1000);
    result := o3;
}

// Helper methods

method numToDigits(num: int) returns (digits: seq<int>)
    requires num >= 1
    ensures |digits| >= 1
    ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
    digits := [];
    var n := num;
    while n > 0
        invariant n >= 0
        invariant |digits| >= 0
        invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
        invariant n == 0 ==> |digits| >= 1
        decreases n
    {
        digits := [n % 10] + digits;
        n := n / 10;
    }
    
    if |digits| == 0 {
        digits := [0];
    }
}

method digitsToNum(digits: seq<int>) returns (num: int)
    requires |digits| >= 1
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures num >= 0
{
    num := 0;
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant num >= 0
    {
        num := num * 10 + digits[i];
        i := i + 1;
    }
}

method replaceDigit(digits: seq<int>, oldDigit: int, newDigit: int) returns (result: seq<int>)
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    requires 0 <= oldDigit <= 9
    requires 0 <= newDigit <= 9
    ensures |result| == |digits|
    ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
{
    result := [];
    var i := 0;
    while i < |digits|
        invariant 0 <= i <= |digits|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 0 <= result[j] <= 9
    {
        if digits[i] == oldDigit {
            result := result + [newDigit];
        } else {
            result := result + [digits[i]];
        }
        i := i + 1;
    }
}

function power10Function(n: int): int
    requires 0 <= n <= 10
    ensures power10Function(n) > 0
{
    if n == 0 then 1
    else 10 * power10Function(n - 1)
}

method createPalindrome(a: int) returns (palindrome: int)
    requires a >= 0
    ensures palindrome >= 0
{
    var b := a;
    palindrome := a;
    
    while b > 0
        invariant b >= 0
        invariant palindrome >= 0
        decreases b
    {
        palindrome := palindrome * 10 + (b % 10);
        b := b / 10;
    }
}
