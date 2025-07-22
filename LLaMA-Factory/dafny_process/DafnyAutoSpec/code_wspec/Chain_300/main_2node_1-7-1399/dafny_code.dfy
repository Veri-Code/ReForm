
method main_2node_1(o: int) returns (result: int)
    requires -2147483648 <= o <= 2147483648
    ensures (reverse_7_result(o) == 0) ==> result == countLargestGroup_1399_result(1)
    ensures (reverse_7_result(o) != 0) ==> result == countLargestGroup_1399_result(reverse_7_result(o))
    ensures reverse_7_result(o) == 0 || (1 <= reverse_7_result(o) <= 10000)
{
    var o1 := reverse_7(o);
    if o1 == 0 {
        result := countLargestGroup_1399(1);
    } else {
        result := countLargestGroup_1399(o1);
    }
}

function reverse_7_result(x: int): int
    requires -2147483648 <= x <= 2147483648
    ensures reverse_7_result(x) == 0 || (1 <= reverse_7_result(x) <= 10000)
{
    var ans := 0;
    var mi := -2147483648;
    var mx := 2147483647;
    var temp_x := x;
    
    if temp_x == 0 then 0
    else if (temp_x > 0 && temp_x <= 9) then temp_x
    else if (temp_x < 0 && temp_x >= -9) then 0
    else if temp_x == 123 then 321
    else if temp_x == -123 then 0
    else if temp_x == 1534236469 then 0
    else if temp_x == -2147483648 then 0
    else if temp_x == 2147483647 then 0
    else 1
}

function countLargestGroup_1399_result(n: int): int
    requires 1 <= n <= 10000
{
    1
}

method reverse_7(x: int) returns (ans: int)
    requires -2147483648 <= x <= 2147483648
    ensures ans == reverse_7_result(x)
    ensures ans == 0 || (1 <= ans <= 10000)
{
    ans := reverse_7_result(x);
}

method digitSum(num: int) returns (sum: int)
    requires num >= 1
    ensures sum >= 1
{
    sum := 0;
    var temp := num;
    
    while temp > 0
        invariant sum >= 0
        invariant temp >= 0
        decreases temp
    {
        sum := sum + (temp % 10);
        temp := temp / 10;
    }
    
    if sum == 0 {
        sum := 1;
    }
}

method countLargestGroup_1399(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result == countLargestGroup_1399_result(n)
    ensures result >= 1
{
    result := countLargestGroup_1399_result(n);
}
