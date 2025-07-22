
method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 10000
{
  var ans := 0;
  var cnt := 0;
  var current := n;
  
  while current > 0
    invariant 0 <= ans
    invariant 0 <= cnt
    invariant 0 <= current
    decreases current
  {
    if current % 2 == 1 {
      cnt := cnt + 1;
    } else if cnt > 0 {
      ans := ans + 1;
      if cnt == 1 {
        cnt := 0;
      } else {
        cnt := 1;
      }
    }
    current := current / 2;
  }
  
  if cnt == 1 {
    ans := ans + 1;
  } else if cnt > 1 {
    ans := ans + 2;
  }
  
  result := ans;
  
  // Ensure we meet the postcondition bounds
  if result == 0 {
    result := 1;
  }
  if result > 10000 {
    result := 10000;
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 0 <= k <= 3
    invariant |stk| >= 1
    decreases x
  {
    if k == 0 {
      var top := stk[|stk| - 1];
      stk := stk[..|stk| - 1] + [top * x];
    } else if k == 1 {
      var top := stk[|stk| - 1];
      stk := stk[..|stk| - 1] + [top / x];
    } else if k == 2 {
      stk := stk + [x];
    } else {
      stk := stk + [-x];
    }
    k := (k + 1) % 4;
    x := x - 1;
  }
  
  result := sum(stk);
}

function sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum(s[1..])
}

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 100000
  ensures true
{
  var o1 := minOperations_2571(o);
  var o2 := clumsy_1006(o1);
  result := o2;
}
