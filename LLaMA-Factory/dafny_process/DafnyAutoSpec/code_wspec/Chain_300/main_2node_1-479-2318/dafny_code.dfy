
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

function power10(n: int): int
  requires 0 <= n <= 8
  ensures power10(n) > 0
{
  if n == 0 then 1
  else if n == 1 then 10
  else if n == 2 then 100
  else if n == 3 then 1000
  else if n == 4 then 10000
  else if n == 5 then 100000
  else if n == 6 then 1000000
  else if n == 7 then 10000000
  else 100000000
}

method createPalindrome(a: int) returns (palindrome: int)
  requires a > 0
  ensures palindrome >= a
{
  var b := a;
  var x := a;
  
  while b > 0
    invariant x >= a
    decreases b
  {
    x := x * 10 + b % 10;
    b := b / 10;
  }
  
  palindrome := x;
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 10000
{
  var mx := power10(n) - 1;
  var minVal := mx / 10;
  
  var a := mx;
  while a > minVal
    invariant minVal <= a <= mx
    decreases a - minVal
  {
    var palindrome := createPalindrome(a);
    
    var t := mx;
    while t * t >= palindrome && t > 0
      invariant t >= 0
      decreases t
    {
      if palindrome % t == 0 {
        result := palindrome % 1337;
        if result == 0 {
          result := 1337;
        }
        return;
      }
      t := t - 1;
    }
    a := a - 1;
  }
  
  result := 9;
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
  
  // Create 3D array dp[n+1][6][6]
  var dp := new int[n + 1, 6, 6];
  
  // Initialize all values to 0
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
  
  // Initialize dp[2][i][j]
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
  
  // Fill dp table for k from 3 to n
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
  
  // Sum all dp[n][i][j]
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

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 8
  ensures result >= 0
{
  var o1 := largestPalindrome_479(o);
  var o2 := distinctSequences_2318(o1);
  result := o2;
}
