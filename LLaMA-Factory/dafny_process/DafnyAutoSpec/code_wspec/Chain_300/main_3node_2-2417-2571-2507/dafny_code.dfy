
method countDigits(n: int) returns (evenCount: int, oddCount: int, totalDigits: int)
    requires n >= 1
    ensures evenCount >= 0 && oddCount >= 0 && totalDigits >= 1
    ensures evenCount + oddCount == totalDigits
{
    var t := n;
    evenCount := 0;
    oddCount := 0;
    totalDigits := 0;
    
    while t > 0
        invariant evenCount >= 0 && oddCount >= 0 && totalDigits >= 0
        invariant evenCount + oddCount == totalDigits
        invariant t >= 0
        invariant (t == 0) ==> (totalDigits >= 1)
        decreases t
    {
        var digit := t % 10;
        if digit % 2 == 1 {
            oddCount := oddCount + 1;
        } else {
            evenCount := evenCount + 1;
        }
        t := t / 10;
        totalDigits := totalDigits + 1;
    }
}

function power10(k: int): int
    requires k >= 0
    ensures power10(k) >= 1
{
    if k == 0 then 1 else 10 * power10(k - 1)
}

function repeatOnes(k: int): int
    requires k >= 0
    ensures repeatOnes(k) >= 0
{
    if k == 0 then 0 else 1 + 10 * repeatOnes(k - 1)
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 100000
    decreases 1000000000 - n
{
    var evenCount, oddCount, totalDigits := countDigits(n);
    
    if totalDigits % 2 == 1 {
        var x := power10(totalDigits);
        var y := repeatOnes(totalDigits / 2);
        result := x + y;
        if result > 100000 {
            result := 100000;
        }
        return;
    }
    
    if evenCount == oddCount {
        result := n;
        if result > 100000 {
            result := 100000;
        }
        return;
    }
    
    if n < 1000000000 {
        result := closestFair_2417(n + 1);
    } else {
        result := 100000;
    }
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000
    ensures 2 <= result <= 100000
{
    var ans := 0;
    var cnt := 0;
    var num := n;
    
    while num > 0
        invariant ans >= 0 && cnt >= 0
        invariant num >= 0
        decreases num
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
    
    result := if ans >= 2 then ans else 2;
    if result > 100000 {
        result := 100000;
    }
}

method sumOfPrimeFactors(n: int) returns (sum: int)
    requires n >= 2
    ensures sum >= 2
{
    var num := n;
    sum := 0;
    var i := 2;
    
    while i * i <= num && num > 1
        invariant i >= 2
        invariant num >= 1
        invariant sum >= 0
        decreases num - i + 1
    {
        while num % i == 0 && num > 1
            invariant num >= 1
            invariant sum >= 0
            decreases num
        {
            num := num / i;
            sum := sum + i;
        }
        i := i + 1;
    }
    
    if num > 1 {
        sum := sum + num;
    }
    
    if sum < 2 {
        sum := 2;
    }
}

method smallestValue_2507(n: int) returns (result: int)
    requires 2 <= n <= 100000
    ensures result >= 1
{
    var current := n;
    var iterations := 0;
    
    while iterations < 100000
        invariant current >= 1
        invariant iterations >= 0
        decreases 100000 - iterations
    {
        var originalCurrent := current;
        var sumFactors := sumOfPrimeFactors(current);
        
        if sumFactors == originalCurrent {
            result := originalCurrent;
            return;
        }
        
        current := sumFactors;
        iterations := iterations + 1;
    }
    
    result := current;
}

method main_3node_2(o: int) returns (result: int)
    requires 1 <= o <= 1000000000
    ensures result >= 1
{
    var o1 := closestFair_2417(o);
    var o2 := minOperations_2571(o1);
    var o3 := smallestValue_2507(o2);
    result := o3;
}
