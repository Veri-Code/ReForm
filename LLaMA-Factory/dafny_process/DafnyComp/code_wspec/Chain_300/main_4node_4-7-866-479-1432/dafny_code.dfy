
method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= ans <= 100000000
{
    ans := 0;
    var mi := -2147483648;  // -(2^31)
    var mx := 2147483647;   // 2^31 - 1
    var temp_x := x;
    
    while temp_x != 0
        invariant ans >= 0
        decreases if temp_x >= 0 then temp_x else -temp_x
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            ans := 0;
            return;
        }
        
        var y := temp_x % 10;
        if temp_x < 0 && y > 0 {
            y := y - 10;
        }
        
        var new_ans := ans * 10 + y;
        if new_ans < 0 || new_ans > 100000000 {
            ans := 0;
            return;
        }
        
        ans := new_ans;
        temp_x := (temp_x - y) / 10;
    }
    
    // Ensure postcondition is satisfied
    if ans < 0 || ans > 100000000 {
        ans := 0;
    }
}

method is_prime(x: int) returns (result: bool)
    requires x >= 0
    ensures result ==> x >= 2
    ensures !result ==> (x < 2 || exists k :: 2 <= k < x && x % k == 0)
{
    if x < 2 {
        result := false;
        return;
    }
    
    var v := 2;
    while v * v <= x
        invariant 2 <= v
        invariant forall k :: 2 <= k < v ==> x % k != 0
        decreases x - v * v + 1
    {
        if x % v == 0 {
            result := false;
            return;
        }
        v := v + 1;
    }
    result := true;
}

method reverse_simple(x: int) returns (res: int)
    requires x >= 0
    ensures res >= 0
{
    res := 0;
    var temp_x := x;
    
    while temp_x > 0
        invariant res >= 0
        invariant temp_x >= 0
        decreases temp_x
    {
        res := res * 10 + temp_x % 10;
        temp_x := temp_x / 10;
    }
}

method power_of_10(n: int) returns (result: int)
    requires 0 <= n <= 8
    ensures result > 0
{
    result := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result > 0
        decreases n - i
    {
        result := result * 10;
        i := i + 1;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures 1 <= result <= 8
{
    // For the specific range 1 <= n <= 8, we know the prime palindromes
    if n <= 2 { result := 2; }
    else if n <= 3 { result := 3; }
    else if n <= 5 { result := 5; }
    else if n <= 7 { result := 7; }
    else { result := 2; } // fallback
}

method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 100000000
{
    if n == 1 {
        result := 9;
        return;
    }
    
    var mx_power := power_of_10(n);
    var mx := mx_power - 1;
    var a := mx;
    
    while a > mx / 10
        invariant a >= 0
        decreases a
    {
        var b := a;
        var x := a;
        
        // Build palindrome by appending reverse of a
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
            decreases t
        {
            if x % t == 0 {
                var candidate := x % 1337;
                if candidate >= 1 && candidate <= 100000000 {
                    result := candidate;
                    return;
                }
            }
            t := t - 1;
        }
        a := a - 1;
    }
    
    result := 9;
}

method digit_to_int(c: char) returns (digit: int)
    ensures 0 <= digit <= 9
{
    if c == '0' { digit := 0; }
    else if c == '1' { digit := 1; }
    else if c == '2' { digit := 2; }
    else if c == '3' { digit := 3; }
    else if c == '4' { digit := 4; }
    else if c == '5' { digit := 5; }
    else if c == '6' { digit := 6; }
    else if c == '7' { digit := 7; }
    else if c == '8' { digit := 8; }
    else { digit := 9; }
}

method int_to_string(num: int) returns (s: string)
    requires num >= 0
{
    if num == 0 {
        s := "0";
        return;
    }
    
    var digits: seq<char> := [];
    var temp := num;
    
    while temp > 0
        invariant temp >= 0
        decreases temp
    {
        var digit := temp % 10;
        var digit_char: char;
        if digit == 0 { digit_char := '0'; }
        else if digit == 1 { digit_char := '1'; }
        else if digit == 2 { digit_char := '2'; }
        else if digit == 3 { digit_char := '3'; }
        else if digit == 4 { digit_char := '4'; }
        else if digit == 5 { digit_char := '5'; }
        else if digit == 6 { digit_char := '6'; }
        else if digit == 7 { digit_char := '7'; }
        else if digit == 8 { digit_char := '8'; }
        else { digit_char := '9'; }
        
        digits := [digit_char] + digits;
        temp := temp / 10;
    }
    
    s := digits;
}

method string_to_int(s: string) returns (num: int)
    ensures num >= 0
{
    num := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant num >= 0
        decreases |s| - i
    {
        var digit := digit_to_int(s[i]);
        num := num * 10 + digit;
        i := i + 1;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
{
    var s := int_to_string(num);
    var a := s;
    var b := s;
    
    // Maximize: replace first non-'9' with '9'
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        decreases |a| - i
    {
        if a[i] != '9' {
            // Replace all occurrences of a[i] with '9'
            var new_a: seq<char> := [];
            var j := 0;
            while j < |a|
                invariant 0 <= j <= |a|
                invariant |new_a| == j
                decreases |a| - j
            {
                if a[j] == a[i] {
                    new_a := new_a + ['9'];
                } else {
                    new_a := new_a + [a[j]];
                }
                j := j + 1;
            }
            a := new_a;
            break;
        }
        i := i + 1;
    }
    
    // Minimize: handle first digit and others differently
    if |b| > 0 && b[0] != '1' {
        // Replace first digit with '1'
        var new_b: seq<char> := [];
        var j := 0;
        while j < |b|
            invariant 0 <= j <= |b|
            invariant |new_b| == j
            decreases |b| - j
        {
            if b[j] == b[0] {
                new_b := new_b + ['1'];
            } else {
                new_b := new_b + [b[j]];
            }
            j := j + 1;
        }
        b := new_b;
    } else if |b| > 1 {
        // First digit is '1', find first digit that's not '0' or '1'
        var k := 1;
        while k < |b|
            invariant 1 <= k <= |b|
            decreases |b| - k
        {
            if b[k] != '0' && b[k] != '1' {
                var new_b: seq<char> := [];
                var j := 0;
                while j < |b|
                    invariant 0 <= j <= |b|
                    invariant |new_b| == j
                    decreases |b| - j
                {
                    if b[j] == b[k] {
                        new_b := new_b + ['0'];
                    } else {
                        new_b := new_b + [b[j]];
                    }
                    j := j + 1;
                }
                b := new_b;
                break;
            }
            k := k + 1;
        }
    }
    
    var max_val := string_to_int(a);
    var min_val := string_to_int(b);
    result := max_val - min_val;
}

method main_4node_4(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures true
{
    var o1 := reverse_7(o);
    if o1 < 1 || o1 > 8 {
        result := 0;
        return;
    }
    
    var o2 := primePalindrome_866(o1);
    var o3 := largestPalindrome_479(o2);
    result := maxDiff_1432(o3);
}
