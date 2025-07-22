
method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 1000000000
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant result >= 0
        invariant result == sumOfMultiplesUpTo(x - 1, n)
        invariant result <= x * n
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    if result == 0 {
        result := 1;
    }
}

function sumOfMultiplesUpTo(current: int, n: int): int
    requires current >= 0
    requires n >= 0
{
    if current <= 0 then 0
    else if current > n then sumOfMultiplesUpTo(n, n)
    else if current % 3 == 0 || current % 5 == 0 || current % 7 == 0 then
        current + sumOfMultiplesUpTo(current - 1, n)
    else
        sumOfMultiplesUpTo(current - 1, n)
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant i >= 0
        invariant a1 >= 1
        decreases cnt
    {
        if i % 2 == 1 {
            an := an - step;
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                an := an - step;
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
}

method main_2node_1(o: int) returns (result: int)
    requires 1 <= o <= 1000
    ensures true
{
    var o1 := sumOfMultiples_2652(o);
    var o2 := lastRemaining_390(o1);
    result := o2;
}
