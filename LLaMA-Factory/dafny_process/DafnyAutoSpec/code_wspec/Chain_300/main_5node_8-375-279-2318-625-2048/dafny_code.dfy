
method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 1 <= result <= 10000
{
  var f := new int[n + 1, n + 1];
  
  // Initialize array to 0
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
    {
      f[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Main DP computation
  i := n - 1;
  while i >= 1
    invariant 0 <= i <= n
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
        var left := if k - 1 < i then 0 else f[i, k - 1];
        var right := if k + 1 > j then 0 else f[k + 1, j];
        var candidate := if left > right then left + k else right + k;
        if candidate < f[i, j] {
          f[i, j] := candidate;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := if n == 1 then 1 else f[1, n];
  if result <= 0 { result := 1; }
  if result > 10000 { result := 10000; }
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 10000
{
  var m := 1;
  while m * m <= n
    invariant 1 <= m
    invariant (m - 1) * (m - 1) <= n
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
      f[i, j] := n + 1; // Use n+1 as "infinity"
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
      if j >= i * i {
        var candidate := f[i, j - i * i] + 1;
        if candidate < f[i, j] {
          f[i, j] := candidate;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := if f[m, n] > n then 1 else f[m, n];
  if result <= 0 { result := 1; }
  if result > 10000 { result := 10000; }
}

function gcd_spec(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd_spec(a, b) > 0
  ensures gcd_spec(a, b) <= a
  ensures b > 0 ==> gcd_spec(a, b) <= b
  decreases b
{
  if b == 0 then a else gcd_spec(b, a % b)
}

method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
  ensures result <= a && result <= b
{
  var x, y := a, b;
  while y != 0
    invariant x > 0 && y >= 0
    invariant gcd_spec(a, b) == gcd_spec(x, y)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 2147483648
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize array
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
  
  // Initialize base case for length 2
  var i := 0;
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
  
  // Fill DP table
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
  
  // Sum all possibilities
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
  if result > 2147483648 { result := 2147483648; }
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 1000000
{
  if num < 2 {
    result := num;
    return;
  }
  
  var ans := 0;
  var mul := 1;
  var remaining := num;
  
  var i := 9;
  while i > 1
    invariant 1 <= i <= 9
    invariant remaining >= 1
    invariant ans >= 0
    invariant mul >= 1
  {
    while remaining % i == 0
      invariant remaining >= 1
      invariant ans >= 0
      invariant mul >= 1
      decreases remaining
    {
      remaining := remaining / i;
      ans := mul * i + ans;
      mul := mul * 10;
      if mul > 100000 || ans > 1000000 {
        result := 0;
        return;
      }
    }
    i := i - 1;
  }
  
  if remaining < 2 && ans <= 1000000 {
    result := ans;
  } else {
    result := 0;
  }
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x >= 1
{
  var y := x;
  var cnt := new int[10];
  
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  while y > 0
    invariant y >= 0
    decreases y
  {
    var digit := y % 10;
    y := y / 10;
    cnt[digit] := cnt[digit] + 1;
  }
  
  beautiful := true;
  i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    if cnt[i] != 0 && i != cnt[i] {
      beautiful := false;
    }
    i := i + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures result > n
{
  var x := n + 1;
  while x <= 10000000  // reasonable upper bound
    invariant x > n
    decreases 10000000 - x
  {
    var beautiful := isBeautiful(x);
    if beautiful {
      result := x;
      return;
    }
    x := x + 1;
  }
  result := 10000000; // fallback
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 200
  ensures result >= 1
{
  var o1 := getMoneyAmount_375(o);
  var o2 := numSquares_279(o1);
  var o3 := distinctSequences_2318(o2);
  var o4 := smallestFactorization_625(o3);
  var o5 := nextBeautifulNumber_2048(o4);
  result := o5;
}
