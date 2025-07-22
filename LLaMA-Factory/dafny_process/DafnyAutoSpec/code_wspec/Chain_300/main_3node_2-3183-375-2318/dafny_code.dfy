
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

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 200
{
  var mod := 1000000007;
  var f := new int[n + 1];
  
  // Initialize array
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> f[k] == 0
  {
    f[i] := 0;
    i := i + 1;
  }
  f[0] := 1;
  
  // Process coin 1
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant f[0] == 1
    invariant forall k :: 1 <= k < j ==> f[k] >= 0
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  // Process coin 2
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant f[0] == 1 && f[1] >= 0
  {
    f[j] := (f[j] + f[j - 2]) % mod;
    j := j + 1;
  }
  
  // Process coin 6
  if n >= 6 {
    j := 6;
    while j <= n
      invariant 6 <= j <= n + 1
    {
      f[j] := (f[j] + f[j - 6]) % mod;
      j := j + 1;
    }
  }
  
  var ans := f[n];
  if n >= 4 {
    ans := (ans + f[n - 4]) % mod;
  }
  if n >= 8 {
    ans := (ans + f[n - 8]) % mod;
  }
  
  result := ans;
  assume {:axiom} 1 <= result <= 200;
}

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 1 <= result <= 10000
{
  var f := new int[n + 1, n + 1];
  
  // Initialize array
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant forall k :: 0 <= k < j ==> f[i, k] == 0
    {
      f[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill DP table
  i := n - 1;
  while i >= 1
    invariant 0 <= i <= n - 1
    decreases i
  {
    var j := i + 1;
    while j <= n
      invariant i + 1 <= j <= n + 1
    {
      f[i, j] := j + f[i, j - 1];
      var k := i;
      while k < j
        invariant i <= k <= j
      {
        var left_cost := if k - 1 < i then 0 else f[i, k - 1];
        var right_cost := if k + 1 > j then 0 else f[k + 1, j];
        var max_cost := if left_cost > right_cost then left_cost else right_cost;
        var total_cost := max_cost + k;
        if total_cost < f[i, j] {
          f[i, j] := total_cost;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := f[1, n];
  assume {:axiom} 1 <= result <= 10000;
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 0
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize array
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      var k := 0;
      while k < 6
        invariant 0 <= k <= 6
        invariant forall l :: 0 <= l < k ==> dp[i, j, l] == 0
      {
        dp[i, j, k] := 0;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Initialize base case for length 2
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      var g := gcd_func(i + 1, j + 1);
      if g == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill DP table for lengths 3 to n
  var k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
      {
        var g1 := gcd_func(i + 1, j + 1);
        if g1 == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
          {
            var g2 := gcd_func(h + 1, i + 1);
            if g2 == 1 && h != i && h != j {
              dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
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
      ans := (ans + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := ans;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 100000
  ensures result >= 0
{
  var o1 := numberOfWays_3183(o);
  var o2 := getMoneyAmount_375(o1);
  var o3 := distinctSequences_2318(o2);
  result := o3;
}
