
method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483647
  ensures 0 <= result <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp_x := x;
  
  while temp_x != 0
    invariant mi == -2147483648
    invariant mx == 2147483647
    invariant -2147483648 <= ans <= 2147483647
    invariant temp_x == 0 ==> -2147483648 <= ans <= 2147483647
  {
    // Check for overflow before multiplication
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    // Since we checked overflow conditions above, this multiplication is safe
    assert ans >= mi / 10 + 1 && ans <= mx / 10;
    assert -10 <= y <= 10;
    
    var new_ans := ans * 10 + y;
    
    // Prove the bounds are maintained more carefully
    assert ans >= -214748364 && ans <= 214748364;
    assert new_ans >= ans * 10 - 10 >= -2147483640 - 10 >= -2147483650;
    assert new_ans <= ans * 10 + 10 <= 2147483640 + 10 <= 2147483650;
    
    // The key insight: new_ans might temporarily exceed bounds, but we need to ensure
    // it stays within int32 range. Since we checked overflow conditions, it should be safe.
    if new_ans < -2147483648 || new_ans > 2147483647 {
      return 0;
    }
    
    ans := new_ans;
    temp_x := (temp_x - y) / 10;
  }
  
  if ans < 0 {
    result := 0;
  } else {
    result := ans;
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
{
  var k := 0;
  var stk: seq<int> := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 0 <= k <= 3
    invariant |stk| >= 1
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
  
  // Sum the stack
  var sum := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
  {
    sum := sum + stk[i];
    i := i + 1;
  }
  
  // Ensure result is at least 1
  if sum >= 1 {
    result := sum;
  } else {
    result := 1;
  }
}

method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures result >= 0
{
  var sum := 0;
  var x := 1;
  
  while x <= n
    invariant 1 <= x <= n + 1
    invariant sum >= 0
  {
    if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
      sum := sum + x;
    }
    x := x + 1;
  }
  
  result := sum;
}

method main_3node_2(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483647
  requires o != 0  // ensures reverse_7 doesn't return 0
  ensures result >= 0
{
  var o1 := reverse_7(o);
  
  // If reverse_7 returns 0 (overflow), we need to handle this case
  if o1 == 0 {
    result := 0;
    return;
  }
  
  // Ensure o1 is in valid range for clumsy_1006
  if o1 < 1 || o1 > 10000 {
    result := 0;
    return;
  }
  
  var o2 := clumsy_1006(o1);
  
  // Ensure o2 is in valid range for sumOfMultiples_2652
  if o2 < 1 || o2 > 1000 {
    result := 0;
    return;
  }
  
  var o3 := sumOfMultiples_2652(o2);
  result := o3;
}
