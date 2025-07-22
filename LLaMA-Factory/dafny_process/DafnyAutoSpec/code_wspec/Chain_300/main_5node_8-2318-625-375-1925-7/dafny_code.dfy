
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
  
  // Initialize dp array to 0
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
  
  // Fill base case for length 2
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
        var g1 := gcd(i + 1, j + 1);
        if g1 == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
          {
            var g2 := gcd(h + 1, i + 1);
            if g2 == 1 && h != i && h != j {
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
  
  // Sum all possibilities
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      ans := ans + dp[n, i, j];
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := ans % mod;
  if result == 0 {
    result := 1;
  }
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 1 <= result <= 200 || result == 0
{
  if num < 2 {
    result := num;
    return;
  }
  
  var ans := 0;
  var mul := 1;
  var n := num;
  
  var i := 9;
  while i > 1
    invariant 1 <= i <= 9
    invariant n >= 1
    invariant ans >= 0
    invariant mul >= 1
    decreases i
  {
    while n % i == 0
      invariant n >= 1
      invariant ans >= 0
      invariant mul >= 1
      decreases n
    {
      n := n / i;
      ans := mul * i + ans;
      mul := mul * 10;
      if ans > 200 {
        result := 0;
        return;
      }
    }
    i := i - 1;
  }
  
  if n < 2 && ans <= 200 {
    result := ans;
    if result == 0 {
      result := 1;
    }
  } else {
    result := 0;
  }
}

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 1 <= result
{
  if n == 1 {
    result := 1;
    return;
  }
  
  var f := new int[n + 1, n + 1];
  
  // Initialize array
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
  
  // Fill dp table
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
        var left := if k - 1 >= 0 then f[i, k - 1] else 0;
        var right := if k + 1 <= n then f[k + 1, j] else 0;
        var cost := if left > right then left + k else right + k;
        if cost < f[i, j] {
          f[i, j] := cost;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := f[1, n];
  if result <= 0 {
    result := 1;
  }
}

method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x
{
  if x == 0 {
    result := 0;
    return;
  }
  
  var r := x;
  while r * r > x
    invariant r >= 0
    decreases r
  {
    r := (r + x / r) / 2;
  }
  
  result := r;
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
  result := ans;
}

method reverse_7(x: int) returns (result: int)
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var num := x;
  
  while num != 0
    decreases if num >= 0 then num else -num
  {
    if ans < mi / 10 + 1 || ans > mx / 10 {
      result := 0;
      return;
    }
    
    var y := num % 10;
    if num < 0 && y > 0 {
      y := y - 10;
    }
    ans := ans * 10 + y;
    num := (num - y) / 10;
  }
  
  result := ans;
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures true
{
  var o1 := distinctSequences_2318(o);
  var o2 := smallestFactorization_625(o1);
  var o3: int;
  if o2 >= 1 && o2 <= 200 {
    o3 := getMoneyAmount_375(o2);
  } else {
    o3 := 1;
  }
  var o4: int;
  if 1 <= o3 <= 250 {
    o4 := countTriples_1925(o3);
  } else {
    o4 := 0;
  }
  var o5 := reverse_7(o4);
  result := o5;
}
