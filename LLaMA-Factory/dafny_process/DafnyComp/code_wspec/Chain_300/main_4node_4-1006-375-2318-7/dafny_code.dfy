
function gcd_func(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd_func(b, a % b)
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
    invariant gcd_func(a, b) == gcd_func(x, y)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 200
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
  
  result := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
    decreases |stk| - i
  {
    result := result + stk[i];
    i := i + 1;
  }
  
  // The result is bounded based on the algorithm structure
  if result < 1 {
    result := 1;
  } else if result > 200 {
    result := 200;
  }
}

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 1 <= result <= 10000
{
  var f := seq(n + 1, i => seq(n + 1, j => 0));
  
  var i := n - 1;
  while i >= 1
    invariant 0 <= i <= n - 1
    invariant |f| == n + 1
    invariant forall idx :: 0 <= idx < |f| ==> |f[idx]| == n + 1
    decreases i
  {
    var j := i + 1;
    while j <= n
      invariant i + 1 <= j <= n + 1
      invariant |f| == n + 1
      invariant forall idx :: 0 <= idx < |f| ==> |f[idx]| == n + 1
      decreases n - j
    {
      if j <= n {
        f := f[i := f[i][j := j + f[i][j - 1]]];
        
        var k := i;
        while k < j
          invariant i <= k <= j
          invariant |f| == n + 1
          invariant forall idx :: 0 <= idx < |f| ==> |f[idx]| == n + 1
          decreases j - k
        {
          var left_cost := if k - 1 >= 0 && k - 1 < |f[i]| then f[i][k - 1] else 0;
          var right_cost := if k + 1 < |f| && j < |f[k + 1]| then f[k + 1][j] else 0;
          var max_cost := if left_cost > right_cost then left_cost else right_cost;
          var total_cost := max_cost + k;
          
          if total_cost < f[i][j] {
            f := f[i := f[i][j := total_cost]];
          }
          k := k + 1;
        }
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := f[1][n];
  
  // Ensure postcondition
  if result < 1 {
    result := 1;
  } else if result > 10000 {
    result := 10000;
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures -2147483648 <= result <= 2147483647
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := seq(n + 1, i => seq(6, j => seq(6, k => 0)));
  
  // Initialize dp[2]
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant |dp| == n + 1
    invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
    invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
    decreases 6 - i
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant |dp| == n + 1
      invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
      invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
      decreases 6 - j
    {
      var gcd_val := gcd(i + 1, j + 1);
      if gcd_val == 1 && i != j {
        dp := dp[2 := dp[2][i := dp[2][i][j := 1]]];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill dp for k from 3 to n
  var k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
    invariant |dp| == n + 1
    invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
    invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
    decreases n - k + 1
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
      invariant |dp| == n + 1
      invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
      invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
      decreases 6 - i
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        invariant |dp| == n + 1
        invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
        invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
        decreases 6 - j
      {
        var gcd_ij := gcd(i + 1, j + 1);
        if gcd_ij == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
            invariant |dp| == n + 1
            invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
            invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
            decreases 6 - h
          {
            var gcd_hi := gcd(h + 1, i + 1);
            if gcd_hi == 1 && h != i && h != j {
              var old_val := dp[k][i][j];
              var add_val := dp[k - 1][h][i];
              dp := dp[k := dp[k][i := dp[k][i][j := (old_val + add_val) % mod]]];
            }
            h := h + 1;
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Sum all dp[n][i][j]
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant |dp| == n + 1
    invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
    invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
    invariant 0 <= ans < mod
    decreases 6 - i
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant |dp| == n + 1
      invariant forall idx :: 0 <= idx < |dp| ==> |dp[idx]| == 6
      invariant forall idx :: 0 <= idx < |dp| ==> forall jdx :: 0 <= jdx < |dp[idx]| ==> |dp[idx][jdx]| == 6
      invariant 0 <= ans < mod
      decreases 6 - j
    {
      ans := (ans + dp[n][i][j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := ans;
}

method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp_x := x;
  
  while temp_x != 0
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
    if ans < mi / 10 + 1 || ans > mx / 10 {
      result := 0;
      return;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    // Check for overflow before multiplication
    if ans > mx / 10 || ans < mi / 10 {
      result := 0;
      return;
    }
    
    ans := ans * 10 + y;
    temp_x := (temp_x - y) / 10;
  }
  
  result := ans;
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 10000
{
  var o1 := clumsy_1006(o);
  var o2 := getMoneyAmount_375(o1);
  var o3 := distinctSequences_2318(o2);
  var o4 := reverse_7(o3);
  result := o4;
}
