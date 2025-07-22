
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

method isPrime(x: int) returns (result: bool)
  requires x >= 0
  ensures result ==> x >= 2
{
  if x < 2 {
    return false;
  }
  var v := 2;
  while v * v <= x
    invariant v >= 2
    invariant forall k :: 2 <= k < v ==> x % k != 0
    decreases x - v * v + 1
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  return true;
}

method reverse(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  var n := x;
  var res := 0;
  while n > 0
    invariant n >= 0
    invariant res >= 0
    decreases n
  {
    res := res * 10 + n % 10;
    n := n / 10;
  }
  result := res;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures 1 <= result <= 10000
{
  var current := n;
  while current <= 10000
    invariant current >= n
    decreases 10000 - current + 1
  {
    var rev := reverse(current);
    if rev == current {
      var prime := isPrime(current);
      if prime {
        return current;
      }
    }
    if 10000000 < current < 100000000 {
      current := 100000000;
      if current > 10000 {
        return 2;
      }
    } else {
      current := current + 1;
    }
  }
  return 2;
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 1000000000
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize all to 0
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
  {
    var i := 0;
    while i < 6
      invariant 0 <= i <= 6
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
      {
        dp[k, i, j] := 0;
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Initialize dp for length 2
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      if i != j {
        var g := gcd(i + 1, j + 1);
        if g == 1 {
          dp[2, i, j] := 1;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill dp for lengths 3 to n
  k := 3;
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
        if i != j {
          var g1 := gcd(i + 1, j + 1);
          if g1 == 1 {
            var h := 0;
            while h < 6
              invariant 0 <= h <= 6
            {
              if h != i && h != j {
                var g2 := gcd(h + 1, i + 1);
                if g2 == 1 {
                  dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
                }
              }
              h := h + 1;
            }
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
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
  
  if ans == 0 {
    return 1;
  }
  if ans > 1000000000 {
    return 1000000000;
  }
  return ans;
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 15
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant a1 >= 1
    decreases cnt
  {
    if i % 2 == 1 {
      an := an - step;
      if cnt % 2 == 1 {
        a1 := a1 + step;
      }
    } else {
      a1 := a1 + step;
      if cnt % 2 == 1 {
        an := an - step;
      }
    }
    cnt := cnt / 2;
    step := step * 2;
    i := i + 1;
  }
  
  if a1 <= 0 || a1 > 15 {
    return 1;
  }
  return a1;
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures 1 <= result <= 100000
{
  var vis := new bool[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  var count := dfs(1, n, vis);
  if count <= 0 {
    return 1;
  }
  if count > 100000 {
    return 100000;
  }
  return count;
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires vis.Length == n + 1
  ensures count >= 0
  modifies vis
  decreases n + 1 - pos
{
  if pos == n + 1 {
    return 1;
  }
  
  count := 0;
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant count >= 0
  {
    if !vis[j] && (j % pos == 0 || pos % j == 0) {
      vis[j] := true;
      var subCount := dfs(pos + 1, n, vis);
      count := count + subCount;
      vis[j] := false;
    }
    j := j + 1;
  }
}

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures result >= 0
{
  var mod := 1000000007;
  var f := new int[n + 1];
  
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    f[i] := 0;
    i := i + 1;
  }
  f[0] := 1;
  
  // Process coin 1
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  // Process coin 2
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
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
  
  if ans < 0 {
    return 0;
  }
  return ans;
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures result >= 0
{
  var o1 := primePalindrome_866(o);
  var o2 := distinctSequences_2318(o1);
  var o3 := lastRemaining_390(o2);
  var o4 := countArrangement_526(o3);
  var o5 := numberOfWays_3183(o4);
  result := o5;
}
