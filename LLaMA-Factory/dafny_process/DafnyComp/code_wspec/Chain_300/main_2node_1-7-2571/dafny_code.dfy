
method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= result <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;  // -(2^31)
  var mx := 2147483647;   // 2^31 - 1
  var temp_x := x;
  
  while temp_x != 0
    invariant 0 <= ans <= 2147483647
    invariant mi == -2147483648
    invariant mx == 2147483647
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
    // Check for potential overflow before multiplication
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    var new_ans := ans * 10 + y;
    if new_ans < 0 || new_ans > 2147483647 {
      return 0;
    }
    
    ans := new_ans;
    temp_x := (temp_x - y) / 10;
  }
  
  result := ans;
}

method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures result >= 0
{
  var ans := 0;
  var cnt := 0;
  var temp_n := n;
  
  while temp_n > 0
    invariant ans >= 0
    invariant cnt >= 0
    invariant temp_n >= 0
    decreases temp_n
  {
    if temp_n % 2 == 1 {  // temp_n is odd
      cnt := cnt + 1;
    } else if cnt > 0 {  // temp_n is even and cnt > 0
      ans := ans + 1;
      if cnt == 1 {
        cnt := 0;
      } else {
        cnt := 1;
      }
    }
    temp_n := temp_n / 2;  // Right shift by 1
  }
  
  if cnt == 1 {
    ans := ans + 1;
  } else if cnt > 1 {
    ans := ans + 2;
  }
  
  result := ans;
}

method main_2node_1(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := reverse_7(o);
  
  if o1 == 0 {
    // If reverse_7 returned 0 due to overflow, we need to handle this case
    // Since minOperations_2571 requires 1 <= n <= 100000, we can't call it with 0
    result := 0;  // or some appropriate default value
  } else if o1 < 1 || o1 > 100000 {
    // If o1 is outside the valid range for minOperations_2571
    result := 0;  // or some appropriate default value
  } else {
    var o2 := minOperations_2571(o1);
    result := o2;
  }
}
