
method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= ans <= 1000000000
{
    ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var curr := x;
    
    while curr != 0
        invariant 0 <= ans <= 1000000000
        decreases if curr >= 0 then curr else -curr
    {
        // Check for overflow before proceeding
        if ans < mi / 10 + 1 || ans > mx / 10 {
            ans := 0;
            return;
        }
        
        var y := curr % 10;
        if curr < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans < 0 || new_ans > 1000000000 {
            ans := 0;
            return;
        }
        
        ans := new_ans;
        curr := (curr - y) / 10;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 1000000000
    decreases 1000000000 - n
{
    var a := 0;
    var b := 0;
    var k := 0;
    var t := n;
    
    // Count odd and even digits
    while t > 0
        invariant t >= 0
        invariant a >= 0 && b >= 0 && k >= 0
        invariant a + b == k
        decreases t
    {
        if (t % 10) % 2 == 1 {
            a := a + 1;
        } else {
            b := b + 1;
        }
        t := t / 10;
        k := k + 1;
    }
    
    // If odd number of digits, construct next even-digit number
    if k % 2 == 1 {
        var x := power10(k);
        var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
        var sum := x + y;
        if sum <= 1000000000 {
            result := sum;
        } else {
            result := 1000000000;
        }
        return;
    }
    
    // If equal number of odd and even digits, return n
    if a == b {
        result := n;
        return;
    }
    
    // Otherwise, recursively check n+1
    if n < 1000000000 {
        result := closestFair_2417(n + 1);
    } else {
        result := 1000000000;
    }
}

function power10(n: int): int
    requires n >= 0
    ensures power10(n) >= 1
{
    if n == 0 then 1
    else 10 * power10(n - 1)
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 2147483647
{
    if n == 1 {
        result := 9;
        return;
    }
    
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant a >= mx / 10
        invariant a <= mx
        decreases a
    {
        var b := a;
        var x := a;
        
        // Create palindrome by mirroring a
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        // Check if x can be expressed as product of two n-digit numbers
        var t := mx;
        while t * t >= x && t > mx / 10
            invariant t >= 0
            decreases t
        {
            if x % t == 0 && x / t <= mx {
                var res := x % 1337;
                if res == 0 {
                    result := 1337;
                } else {
                    result := res;
                }
                return;
            }
            t := t - 1;
        }
        
        a := a - 1;
    }
    
    result := 9;
}

method integerReplacement_397(n: int) returns (ans: int)
    requires 1 <= n <= 2147483647
    ensures ans >= 0
{
    ans := 0;
    var curr := n;
    
    while curr != 1
        invariant curr >= 1
        invariant ans >= 0
        invariant ans <= 50
        decreases 50 - ans
    {
        if ans >= 50 {
            break;
        }
        
        if curr % 2 == 0 {
            curr := curr / 2;
        } else if curr != 3 && curr % 4 == 3 {
            curr := curr + 1;
        } else {
            curr := curr - 1;
        }
        ans := ans + 1;
    }
}

method main_4node_4(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures result >= 0
{
    var o1 := reverse_7(o);
    
    if o1 == 0 {
        result := integerReplacement_397(1);
        return;
    }
    
    var o2 := closestFair_2417(o1);
    var o3 := largestPalindrome_479(if 1 <= o2 <= 8 then o2 else 1);
    result := integerReplacement_397(if o3 >= 1 then o3 else 1);
}
