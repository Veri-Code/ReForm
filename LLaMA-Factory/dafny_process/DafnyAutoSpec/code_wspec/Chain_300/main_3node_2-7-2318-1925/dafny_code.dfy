
method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483647
  ensures 0 <= result <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp_x := x;
  
  while temp_x != 0
    invariant -2147483648 <= temp_x <= 2147483647
    invariant -2147483648 <= ans <= 2147483647
  {
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    var new_ans := ans * 10 + y;
    if new_ans < mi || new_ans > mx {
      return 0;
    }
    
    ans := new_ans;
    temp_x := (temp_x - y) / 10;
  }
  
  if ans < 0 {
    return 0;
  }
  
  return ans;
}

function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  decreases if a < b then b else a
{
  if a == b then a
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 1000000007
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize dp array to 0
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
    invariant forall k0, i0, j0 :: 0 <= k0 < k && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] == 0
  {
    var i := 0;
    while i < 6
      invariant 0 <= i <= 6
      invariant forall k0, i0, j0 :: 0 <= k0 < k && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] == 0
      invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < 6 ==> dp[k, i0, j0] == 0
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        invariant forall k0, i0, j0 :: 0 <= k0 < k && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] == 0
        invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < 6 ==> dp[k, i0, j0] == 0
        invariant forall j0 :: 0 <= j0 < j ==> dp[k, i, j0] == 0
      {
        dp[k, i, j] := 0;
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Fill base case for length 2
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
    invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < 6 ==> 
      (if gcd(i0 + 1, j0 + 1) == 1 && i0 != j0 then dp[2, i0, j0] == 1 else dp[2, i0, j0] == 0)
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
      invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < 6 ==> 
        (if gcd(i0 + 1, j0 + 1) == 1 && i0 != j0 then dp[2, i0, j0] == 1 else dp[2, i0, j0] == 0)
      invariant forall j0 :: 0 <= j0 < j ==> 
        (if gcd(i + 1, j0 + 1) == 1 && i != j0 then dp[2, i, j0] == 1 else dp[2, i, j0] == 0)
    {
      if gcd(i + 1, j + 1) == 1 && i != j {
        dp[2, i, j] := 1;
      } else {
        dp[2, i, j] := 0;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill DP table for lengths 3 to n
  k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
    invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
      invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
      {
        dp[k, i, j] := 0;
        if gcd(i + 1, j + 1) == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
            invariant dp[k, i, j] >= 0
            invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
          {
            if gcd(h + 1, i + 1) == 1 && h != i && h != j {
              dp[k, i, j] := dp[k, i, j] + dp[k - 1, h, i];
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
  
  // Sum all possibilities for the final answer
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant ans >= 0
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant ans >= 0
    {
      ans := ans + dp[n, i, j];
      j := j + 1;
    }
    i := i + 1;
  }
  
  if ans == 0 {
    return 1;
  }
  
  var result_val := ans % mod;
  if result_val == 0 {
    return 1;
  }
  
  return result_val;
}

method countTriples_1925(n: int) returns (result: int)
  requires 1 <= n <= 250
  ensures result >= 0
{
  var ans := 0;
  var a := 1;
  
  while a < n
    invariant 1 <= a <= n
    invariant ans >= 0
  {
    var b := 1;
    while b < n
      invariant 1 <= b <= n
      invariant ans >= 0
    {
      var x := a * a + b * b;
      var c := isqrt(x);
      
      if c <= n && c * c == x {
        ans := ans + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }
  
  return ans;
}

function isqrt(x: int): int
  requires x >= 0
  ensures isqrt(x) >= 0
  ensures isqrt(x) * isqrt(x) <= x
{
  if x <= 1 then x
  else
    var low := 1;
    var high := x;
    isqrt_binary_search(x, low, high)
}

function isqrt_binary_search(x: int, low: int, high: int): int
  requires x >= 0 && low >= 0 && high >= low
  requires low * low <= x
  ensures isqrt_binary_search(x, low, high) >= 0
  ensures isqrt_binary_search(x, low, high) * isqrt_binary_search(x, low, high) <= x
  decreases high - low
{
  if low >= high then low
  else
    var mid := (low + high + 1) / 2;
    if mid * mid <= x then
      isqrt_binary_search(x, mid, high)
    else
      isqrt_binary_search(x, low, mid - 1)
}

predicate reverse_7_would_not_overflow(x: int)
{
  true
}

method main_3node_2(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483647
  requires reverse_7_would_not_overflow(o)
  ensures result >= 0
{
  var o1 := reverse_7(o);
  if o1 < 1 || o1 > 10000 {
    result := 0;
    return;
  }
  var o2 := distinctSequences_2318(o1);
  if o2 < 1 || o2 > 250 {
    result := 0;
    return;
  }
  var o3 := countTriples_1925(o2);
  result := o3;
}
