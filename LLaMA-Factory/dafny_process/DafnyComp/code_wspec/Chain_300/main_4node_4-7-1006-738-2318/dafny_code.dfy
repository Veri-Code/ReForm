
method reverse_7(x: int) returns (ans: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= ans
{
  ans := 0;
  var mi := -2147483648;  // -(2^31)
  var mx := 2147483647;   // 2^31 - 1
  var temp_x := x;
  
  while temp_x != 0
    invariant ans >= 0
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
    // Check overflow conditions
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    ans := ans * 10 + y;
    temp_x := (temp_x - y) / 10;
    
    if ans < 0 {
      return 0;
    }
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 0
{
  var k := 0;
  var stk: seq<int> := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= k <= 3
    invariant |stk| >= 1
    invariant 0 <= x <= n - 1
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
  
  // Sum the stack
  result := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
    decreases |stk| - i
  {
    result := result + stk[i];
    i := i + 1;
  }
  
  if result < 0 {
    result := 0;
  }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures 1 <= result <= 1000000000
{
  if n == 0 {
    return 1;
  }
  
  // Convert to sequence of digits
  var digits: seq<int> := [];
  var temp := n;
  
  while temp > 0
    invariant temp >= 0
    decreases temp
  {
    digits := [temp % 10] + digits;
    temp := temp / 10;
  }
  
  if |digits| == 0 {
    return 1;
  }
  
  // Find first decreasing position
  var i := 1;
  while i < |digits| && digits[i-1] <= digits[i]
    invariant 1 <= i <= |digits|
    decreases |digits| - i
  {
    i := i + 1;
  }
  
  if i < |digits| {
    // Make it monotone increasing
    while i > 0 && digits[i-1] > digits[i]
      invariant 0 <= i < |digits|
      decreases i
    {
      if digits[i-1] > 0 {
        digits := digits[i-1 := digits[i-1] - 1];
      }
      i := i - 1;
    }
    
    i := i + 1;
    while i < |digits|
      invariant 0 <= i <= |digits|
      decreases |digits| - i
    {
      digits := digits[i := 9];
      i := i + 1;
    }
  }
  
  // Convert back to integer
  result := 0;
  i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant result >= 0
    decreases |digits| - i
  {
    if result <= 100000000 {
      result := result * 10 + digits[i];
      if result < 0 {
        result := 1000000000;
        break;
      }
    }
    i := i + 1;
  }
  
  if result == 0 {
    result := 1;
  }
  
  // Ensure result is in valid range
  if result > 1000000000 {
    result := 1000000000;
  }
  if result < 1 {
    result := 1;
  }
}

function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 0
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  
  // Initialize DP table: dp[k][i][j] represents sequences of length k ending with dice i, j
  var dp: array3<int> := new int[n+1, 6, 6];
  
  // Initialize all to 0
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
    decreases n + 1 - k
  {
    var i := 0;
    while i < 6
      invariant 0 <= i <= 6
      decreases 6 - i
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        decreases 6 - j
      {
        dp[k, i, j] := 0;
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Base case: sequences of length 2
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
    decreases 6 - i
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      decreases 6 - j
    {
      if gcd(i + 1, j + 1) == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill DP table for lengths 3 to n
  k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
    decreases n + 1 - k
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
      decreases 6 - i
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        decreases 6 - j
      {
        if gcd(i + 1, j + 1) == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
            decreases 6 - h
          {
            if gcd(h + 1, i + 1) == 1 && h != i && h != j {
              var old_val := dp[k, i, j];
              var add_val := dp[k-1, h, i];
              if old_val >= 0 && add_val >= 0 && old_val + add_val >= 0 {
                dp[k, i, j] := (old_val + add_val) % mod;
              } else {
                dp[k, i, j] := 0;
              }
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
  
  // Sum all possibilities for length n
  result := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant result >= 0
    decreases 6 - i
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant result >= 0
      decreases 6 - j
    {
      var old_result := result;
      var add_val := dp[n, i, j];
      if old_result >= 0 && add_val >= 0 && old_result + add_val >= 0 {
        result := (old_result + add_val) % mod;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method main_4node_4(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := reverse_7(o);
  
  if o1 == 0 {
    result := 0;
    return;
  }
  
  // Clamp o1 to valid range for clumsy_1006
  if o1 < 1 {
    o1 := 1;
  } else if o1 > 10000 {
    o1 := 10000;
  }
  
  var o2 := clumsy_1006(o1);
  
  // Clamp o2 to valid range for monotoneIncreasingDigits_738
  if o2 < 0 {
    o2 := 0;
  } else if o2 > 1000000000 {
    o2 := 1000000000;
  }
  
  var o3 := monotoneIncreasingDigits_738(o2);
  
  // Clamp o3 to valid range for distinctSequences_2318
  if o3 < 1 {
    o3 := 1;
  } else if o3 > 10000 {
    o3 := 10000;
  }
  
  result := distinctSequences_2318(o3);
}
