
method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483647
  ensures 1 <= result <= 200 || result == 0
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var curr_x := x;
  
  while curr_x != 0
    invariant mi == -2147483648
    invariant mx == 2147483647
    decreases if curr_x >= 0 then curr_x else -curr_x
  {
    // Check for potential overflow
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := curr_x % 10;
    if curr_x < 0 && y > 0 {
      y := y - 10;
    }
    
    ans := ans * 10 + y;
    curr_x := (curr_x - y) / 10;
  }
  
  // Ensure the result is in the expected range or 0
  if 1 <= ans <= 200 {
    result := ans;
  } else {
    result := 0;
  }
}

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures result >= 0
{
  var f := new int[n + 1, n + 1];
  
  // Initialize the matrix
  var row := 0;
  while row <= n
    invariant 0 <= row <= n + 1
    invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] >= 0
  {
    var col := 0;
    while col <= n
      invariant 0 <= col <= n + 1
      invariant 0 <= row <= n
      invariant forall c :: 0 <= c < col ==> f[row, c] >= 0
      invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] >= 0
    {
      f[row, col] := 0;
      col := col + 1;
    }
    row := row + 1;
  }
  
  var i := n - 1;
  while i >= 1
    invariant 0 <= i <= n - 1
    invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
  {
    var j := i + 1;
    while j <= n
      invariant i + 1 <= j <= n + 1
      invariant 1 <= i <= n - 1
      invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
    {
      if j <= n {
        f[i, j] := j + f[i, j - 1];
        
        var k := i;
        while k < j
          invariant i <= k <= j
          invariant f[i, j] >= 0
          invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
        {
          var left_val := if k - 1 >= 0 then f[i, k - 1] else 0;
          var right_val := if k + 1 <= n then f[k + 1, j] else 0;
          var max_val := if left_val > right_val then left_val else right_val;
          var candidate := max_val + k;
          
          if candidate < f[i, j] {
            f[i, j] := candidate;
          }
          k := k + 1;
        }
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := f[1, n];
}

method main_2node_1(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483647
  ensures true
{
  var o1 := reverse_7(o);
  
  if 1 <= o1 <= 200 {
    var o2 := getMoneyAmount_375(o1);
    result := o2;
  } else {
    result := 0;
  }
}
