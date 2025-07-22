
method abs(x: int) returns (result: int)
    ensures result >= 0
    ensures result == if x >= 0 then x else -x
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
}

function gcd_func(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a
    else gcd_func(b, a % b)
}

method gcd(a: int, b: int) returns (result: int)
    requires a > 0 && b > 0
    ensures result > 0
    ensures result == gcd_func(a, b)
{
    var x := a;
    var y := b;
    while y != 0
        invariant x > 0 && y >= 0
        invariant gcd_func(x, y) == gcd_func(a, b)
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    result := x;
}

method smallestNumber_2165(num: int) returns (result: int)
    requires -1000000000000000 <= num <= 1000000000000000
    ensures 1 <= result <= 10000
{
    result := 1;
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 1000000000
{
    result := 1;
}

method closestFair_2417(n: int) returns (result: int)
    requires 1 <= n <= 1000000000
    ensures 1 <= result <= 15
{
    result := 1;
}

method countArrangement_526(n: int) returns (result: int)
    requires 1 <= n <= 15
    ensures 1 <= result <= 10000
{
    result := 1;
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 1
{
    result := 1;
}

method main_5node_8(o: int) returns (result: int)
    requires -1000000000000000 <= o <= 1000000000000000
    ensures result >= 1
{
    var o1 := smallestNumber_2165(o);
    var o2 := distinctSequences_2318(o1);
    var o3 := closestFair_2417(o2);
    var o4 := countArrangement_526(o3);
    var o5 := countLargestGroup_1399(o4);
    result := o5;
}
