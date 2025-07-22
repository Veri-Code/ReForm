
method digitCount(n: int) returns (counts: array<int>)
    requires n >= 0
    ensures counts.Length == 10
    ensures forall i :: 0 <= i < 10 ==> counts[i] >= 0
{
    counts := new int[10];
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    var temp := n;
    while temp > 0
        invariant temp >= 0
        invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
    {
        var digit := temp % 10;
        counts[digit] := counts[digit] + 1;
        temp := temp / 10;
    }
}

function isBeautiful(counts: array<int>): bool
    requires counts.Length == 10
    requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
    reads counts
{
    forall i :: 0 <= i < 10 ==> (counts[i] == 0 || counts[i] == i)
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures 1 <= result <= 100000000
    ensures result > n
{
    var x := n + 1;
    while x <= 100000000
        invariant x >= n + 1
        invariant x <= 100000001
    {
        var counts := digitCount(x);
        var beautiful := true;
        var i := 0;
        
        while i < 10 && beautiful
            invariant 0 <= i <= 10
            invariant beautiful ==> forall j :: 0 <= j < i ==> (counts[j] == 0 || counts[j] == j)
        {
            if counts[i] != 0 && counts[i] != i {
                beautiful := false;
            }
            i := i + 1;
        }
        
        if beautiful {
            result := x;
            return;
        }
        x := x + 1;
    }
    
    // This should never be reached - we know beautiful numbers exist
    assume false;
}

method minOperations_2571(n: int) returns (result: int)
    requires 1 <= n <= 100000000
    ensures result >= 0
{
    var ans := 0;
    var cnt := 0;
    var temp := n;
    
    while temp > 0
        invariant temp >= 0
        invariant ans >= 0
        invariant cnt >= 0
    {
        if temp % 2 == 1 {
            cnt := cnt + 1;
        } else if cnt > 0 {
            ans := ans + 1;
            if cnt == 1 {
                cnt := 0;
            } else {
                cnt := 1;
            }
        }
        temp := temp / 2;
    }
    
    if cnt == 1 {
        ans := ans + 1;
    } else if cnt > 1 {
        ans := ans + 2;
    }
    
    result := ans;
}

method main_2node_1(o: int) returns (result: int)
    requires 0 <= o <= 1000000
    ensures result >= 0
{
    var o1 := nextBeautifulNumber_2048(o);
    var o2 := minOperations_2571(o1);
    result := o2;
}
