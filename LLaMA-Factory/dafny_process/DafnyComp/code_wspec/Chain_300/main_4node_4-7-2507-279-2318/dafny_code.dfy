
method reverse_7(x: int) returns (ans: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= ans <= 2147483647
{
  ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp_x := x;
  
  while temp_x != 0
    invariant 0 <= ans <= 2147483647
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
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
}

function gcd_spec(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd_spec(b, a % b)
}

method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
  ensures result == gcd_spec(a, b)
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

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 100000
  decreases *
{
  var current := n;
  var iterations := 0;
  
  while iterations < 1000000
    invariant 2 <= current <= 1000000
    invariant iterations >= 0
    decreases 1000000 - iterations
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp_n := current;
    
    while i * i <= temp_n
      invariant 2 <= i
      invariant s >= 0
      invariant temp_n >= 1
      decreases temp_n - i + 1
    {
      while temp_n % i == 0
        invariant temp_n >= 1
        invariant s >= 0
        decreases temp_n
      {
        temp_n := temp_n / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    if temp_n > 1 {
      s := s + temp_n;
    }
    
    if s == t {
      if s <= 100000 {
        return s;
      } else {
        return 100000;
      }
    }
    
    if s > 1000000 || s < 2 {
      return 100000;
    }
    current := s;
    iterations := iterations + 1;
  }
  
  if current <= 100000 {
    return current;
  } else {
    return 100000;
  }
}

method sqrt_int(n: int) returns (result: int)
  requires n >= 0
  ensures result >= 0
  ensures result * result <= n < (result + 1) * (result + 1)
{
  if n == 0 { return 0; }
  
  var x := 0;
  while (x + 1) * (x + 1) <= n
    invariant x >= 0
    invariant x * x <= n
    decreases n - x * x
  {
    x := x + 1;
  }
  result := x;
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 10000
{
  var m := sqrt_int(n);
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
      f[i, j] := 10001;
      j := j + 1;
    }
    i := i + 1;
  }
  
  f[0, 0] := 0;
  
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant f[0, 0] == 0
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant f[0, 0] == 0
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
  
  result := f[m, n];
  if result > 10000 {
    result := 10000;
  }
  if result < 1 {
    result := 1;
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 0
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
  
  // Initialize base case for length 2
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      var gcd_val := gcd(i + 1, j + 1);
      if gcd_val == 1 && i != j {
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
        var gcd_ij := gcd(i + 1, j + 1);
        if gcd_ij == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
          {
            var gcd_hi := gcd(h + 1, i + 1);
            if gcd_hi == 1 && h != i && h != j {
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

method main_4node_4(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures result >= 0
  decreases *
{
  var o1 := reverse_7(o);
  if o1 == 0 {
    result := 0;
    return;
  }
  if o1 < 2 {
    result := 0;
    return;
  }
  if o1 > 100000 {
    result := 0;
    return;
  }
  
  var o2 := smallestValue_2507(o1);
  if o2 > 10000 {
    result := 0;
    return;
  }
  var o3 := numSquares_279(o2);
  result := distinctSequences_2318(o3);
}
