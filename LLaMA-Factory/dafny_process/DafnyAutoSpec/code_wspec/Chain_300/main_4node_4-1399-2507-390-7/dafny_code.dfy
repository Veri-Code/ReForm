
method digitSum(n: int) returns (sum: int)
    requires n >= 1
    ensures sum >= 1
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant sum >= 0
        invariant temp >= 0
        invariant n >= 1 ==> (temp > 0 || sum > 0)
        decreases temp
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result
{
    var counts := new int[46];
    var i := 0;
    while i < counts.Length
        invariant 0 <= i <= counts.Length
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
        invariant maxCount > 0 ==> answer >= 1
    {
        var ds := digitSum(i);
        if ds < counts.Length {
            counts[ds] := counts[ds] + 1;
            
            if maxCount < counts[ds] {
                maxCount := counts[ds];
                answer := 1;
            } else if maxCount == counts[ds] {
                answer := answer + 1;
            }
        }
        i := i + 1;
    }
    
    result := if answer == 0 then 1 else answer;
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures 1 <= result <= 1000000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000
        invariant current >= 1
        invariant iterations >= 0
        decreases 1000 - iterations
    {
        var original := current;
        var sum := 0;
        var temp := current;
        var i := 2;
        
        while i * i <= temp && temp > 1
            invariant sum >= 0
            invariant temp >= 1
            invariant i >= 2
            invariant current >= 1
        {
            while temp % i == 0 && temp > 1
                invariant temp >= 1
                invariant i >= 2
                decreases temp
            {
                temp := temp / i;
                sum := sum + i;
            }
            i := i + 1;
        }
        
        if temp > 1 {
            sum := sum + temp;
        }
        
        if sum == original {
            result := if original <= 1000000 then original else 1000000;
            return;
        }
        
        current := if sum >= 1 then sum else 1;
        iterations := iterations + 1;
    }
    
    result := if current <= 1000000 then current else 1000000;
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
        invariant step <= n
        invariant a1 >= 1
        invariant an >= 1
        invariant a1 <= n
        invariant an <= n
        decreases cnt
    {
        if i % 2 == 0 {
            var new_a1 := a1 + step;
            if new_a1 <= n {
                a1 := new_a1;
            }
            if cnt % 2 == 1 {
                var new_an := an - step;
                if new_an >= 1 {
                    an := new_an;
                }
            }
        } else {
            var new_an := an - step;
            if new_an >= 1 {
                an := new_an;
            }
            if cnt % 2 == 1 {
                var new_a1 := a1 + step;
                if new_a1 <= n {
                    a1 := new_a1;
                }
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

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483647
    ensures true
{
    var ans := 0;
    var temp := x;
    var mi := -2147483648;
    var mx := 2147483647;
    
    while temp != 0
        decreases if temp >= 0 then temp else -temp
    {
        if ans < mi / 10 || ans > mx / 10 {
            result := 0;
            return;
        }
        
        var digit := temp % 10;
        if temp < 0 && digit > 0 {
            digit := digit - 10;
        }
        
        if (ans == mi / 10 && digit < mi % 10) || 
           (ans == mx / 10 && digit > mx % 10) {
            result := 0;
            return;
        }
        
        ans := ans * 10 + digit;
        temp := (temp - digit) / 10;
    }
    
    result := ans;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures true
{
    var o1 := countLargestGroup_1399(o);
    var o2 := smallestValue_2507(if o1 >= 2 then (if o1 <= 100000 then o1 else 100000) else 2);
    var o3 := lastRemaining_390(if o2 <= 1000000000 then o2 else 1000000000);
    var o4 := reverse_7(o3);
    result := o4;
}
