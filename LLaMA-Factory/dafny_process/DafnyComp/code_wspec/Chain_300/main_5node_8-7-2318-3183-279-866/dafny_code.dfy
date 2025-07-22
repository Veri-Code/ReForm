
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

method reverse_7(x: int) returns (ans: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= ans <= 10000
{
  ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var curr := x;
  
  while curr != 0
    invariant 0 <= ans <= 10000
    decreases if curr >= 0 then curr else -curr
  {
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    var y := curr % 10;
    if curr < 0 && y > 0 {
      y := y - 10;
    }
    if ans > 1000 || ans < -1000 {
      return 0;
    }
    var new_ans := ans * 10 + y;
    if new_ans < 0 || new_ans > 10000 {
      return 0;
    }
    ans := new_ans;
    curr := (curr - y) / 10;
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 100000
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize all to 0
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
      {
        dp[i, j, k] := 0;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill dp[2]
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      var g := gcd(i + 1, j + 1);
      if g == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill dp[3..n]
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
        var g1 := gcd(i + 1, j + 1);
        if g1 == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
          {
            var g2 := gcd(h + 1, i + 1);
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
  
  // Sum all dp[n][i][j]
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant 0 <= ans
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant 0 <= ans
    {
      ans := (ans + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := if ans == 0 then 1 else ans;
  if result > 100000 {
    result := 100000;
  }
  if result < 1 {
    result := 1;
  }
}

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 10000
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
    invariant f[0] == 1
    invariant forall k :: 0 <= k < j ==> f[k] >= 0
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  // Process coin 2
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant forall k :: 0 <= k < j ==> f[k] >= 0
  {
    f[j] := (f[j] + f[j - 2]) % mod;
    j := j + 1;
  }
  
  // Process coin 6
  if n >= 6 {
    j := 6;
    while j <= n
      invariant 6 <= j <= n + 1
      invariant forall k :: 0 <= k < j ==> f[k] >= 0
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
  
  result := if ans == 0 then 1 else ans;
  if result > 10000 {
    result := 10000;
  }
  if result < 1 {
    result := 1;
  }
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 100000000
{
  var m := 1;
  while m * m <= n
    invariant 1 <= m
    invariant (m - 1) * (m - 1) <= n
    decreases n - (m - 1) * (m - 1)
  {
    m := m + 1;
  }
  m := m - 1;
  
  var f := new int[m + 1, n + 1];
  
  // Initialize with large values
  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
    {
      f[i, j] := 100000000;
      j := j + 1;
    }
    i := i + 1;
  }
  f[0, 0] := 0;
  
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
    {
      f[i, j] := f[i - 1, j];
      if j >= i * i && f[i, j - i * i] < 100000000 {
        var candidate := f[i, j - i * i] + 1;
        if candidate < f[i, j] {
          f[i, j] := candidate;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := f[m, n];
  if result < 1 {
    result := 1;
  }
  if result > 100000000 {
    result := 100000000;
  }
}

method is_prime(x: int) returns (result: bool)
  requires x >= 0
{
  if x < 2 {
    return false;
  }
  var v := 2;
  while v * v <= x
    invariant 2 <= v
    invariant forall k :: 2 <= k < v ==> x % k != 0
    decreases x - v * v + 1
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  result := true;
}

method reverse_num(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  result := 0;
  var curr := x;
  while curr > 0
    invariant curr >= 0
    invariant result >= 0
    decreases curr
  {
    result := result * 10 + curr % 10;
    curr := curr / 10;
  }
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures result >= 2
{
  var curr := n;
  while true
    invariant curr >= n
    invariant curr >= 1
    decreases 200000000 - curr
  {
    if curr > 200000000 {
      return 2; // fallback
    }
    if curr >= 2 {
      var rev := reverse_num(curr);
      if rev == curr {
        var prime := is_prime(curr);
        if prime {
          return curr;
        }
      }
    }
    if 10000000 < curr < 100000000 {
      curr := 100000000;
    } else {
      curr := curr + 1;
    }
  }
}

method main_5node_8(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures result >= 2
{
  var o1 := reverse_7(o);
  if o1 == 0 {
    return 2;
  }
  var o2 := distinctSequences_2318(o1);
  var o3 := numberOfWays_3183(o2);
  var o4 := numSquares_279(o3);
  var o5 := primePalindrome_866(o4);
  result := o5;
}
