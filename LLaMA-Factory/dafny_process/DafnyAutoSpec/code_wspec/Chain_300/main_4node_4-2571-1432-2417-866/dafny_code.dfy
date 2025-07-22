
method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 1 <= result <= 100000000
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant ans >= 0
        invariant cnt >= 0
        invariant num >= 0
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
    if result == 0 {
        result := 1;
    }
    
    assert result >= 1;
    if result > 100000000 {
        result := 100000000;
    }
}

method maxDiff_1432(num: int) returns (result: int)
    requires 1 <= num <= 100000000
    ensures 1 <= result <= 1000000000
{
    var maxNum := num;
    var minNum := num;
    
    var temp := num;
    var multiplier := 1;
    var found := false;
    
    while temp > 0
        invariant temp >= 0
        invariant multiplier >= 1
    {
        var digit := temp % 10;
        if digit != 9 && !found {
            maxNum := maxNum + (9 - digit) * multiplier;
            found := true;
        }
        temp := temp / 10;
        multiplier := multiplier * 10;
    }
    
    temp := num;
    multiplier := 1;
    found := false;
    var isFirstDigit := true;
    var numDigits := 0;
    var tempForCount := num;
    
    while tempForCount > 0
        invariant tempForCount >= 0
    {
        numDigits := numDigits + 1;
        tempForCount := tempForCount / 10;
    }
    
    var currentPos := 0;
    while temp > 0
        invariant temp >= 0
        invariant multiplier >= 1
        invariant currentPos >= 0
    {
        var digit := temp % 10;
        isFirstDigit := (currentPos == numDigits - 1);
        
        if isFirstDigit && digit != 1 && !found {
            minNum := minNum - (digit - 1) * multiplier;
            found := true;
        } else if !isFirstDigit && digit != 0 && digit != 1 && !found {
            minNum := minNum - digit * multiplier;
            found := true;
        }
        
        temp := temp / 10;
        multiplier := multiplier * 10;
        currentPos := currentPos + 1;
    }
    
    result := maxNum - minNum;
    if result <= 0 {
        result := 1;
    }
    
    assert result >= 1;
    if result > 1000000000 {
        result := 1000000000;
    }
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000000
{
    var current := n;
    var iterations := 0;
    
    while iterations < 1000000
        invariant current >= 1
        invariant iterations >= 0
    {
        var evenCount := 0;
        var oddCount := 0;
        var temp := current;
        var digitCount := 0;
        
        while temp > 0
            invariant temp >= 0
            invariant evenCount >= 0
            invariant oddCount >= 0
            invariant digitCount >= 0
        {
            var digit := temp % 10;
            if digit % 2 == 0 {
                evenCount := evenCount + 1;
            } else {
                oddCount := oddCount + 1;
            }
            digitCount := digitCount + 1;
            temp := temp / 10;
        }
        
        if digitCount % 2 == 1 {
            var power := 1;
            var i := 0;
            while i < digitCount
                invariant power >= 1
                invariant i >= 0
            {
                power := power * 10;
                i := i + 1;
            }
            result := power + power / 20;
            if result > 100000000 {
                result := 100000000;
            }
            return;
        }
        
        if evenCount == oddCount {
            result := current;
            if result > 100000000 {
                result := 100000000;
            }
            return;
        }
        
        current := current + 1;
        iterations := iterations + 1;
    }
    
    result := 1001;
}

method isPrime(x: int) returns (result: bool)
    requires x >= 1
{
    if x < 2 {
        result := false;
        return;
    }
    
    if x == 2 {
        result := true;
        return;
    }
    
    if x % 2 == 0 {
        result := false;
        return;
    }
    
    var v := 3;
    while v * v <= x
        invariant v >= 3
        invariant v % 2 == 1
    {
        if x % v == 0 {
            result := false;
            return;
        }
        v := v + 2;
    }
    
    result := true;
}

method reverseNumber(x: int) returns (result: int)
    requires x >= 0
    ensures result >= 0
{
    result := 0;
    var temp := x;
    
    while temp > 0
        invariant temp >= 0
        invariant result >= 0
    {
        result := result * 10 + temp % 10;
        temp := temp / 10;
    }
}

method primePalindrome_866(n: int) returns (result: int)
    requires 1 <= n
    ensures result >= 2
{
    if n <= 2 {
        result := 2;
        return;
    }
    
    var current := n;
    var iterations := 0;
    
    while iterations < 1000000
        invariant current >= 1
        invariant iterations >= 0
    {
        var reversed := reverseNumber(current);
        var isPalin := (reversed == current);
        
        if isPalin {
            var prime := isPrime(current);
            if prime {
                result := current;
                assert result >= 2;
                return;
            }
        }
        
        if 10000000 < current < 100000000 {
            current := 100000000;
        } else {
            current := current + 1;
        }
        iterations := iterations + 1;
    }
    
    result := 100030001;
}

method main_4node_4(o: int) returns (result: int)
    requires 1 <= o <= 100000
    ensures result >= 2
{
    var o1 := minOperations_2571(o);
    var o2 := maxDiff_1432(o1);
    var o3 := closestFair_2417(o2);
    var o4 := primePalindrome_866(o3);
    result := o4;
}
