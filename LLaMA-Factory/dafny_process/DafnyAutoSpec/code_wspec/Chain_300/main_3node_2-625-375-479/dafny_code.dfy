
method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 2147483647
{
  if num < 2 {
    return num;
  }
  
  var ans := 0;
  var mul := 1;
  var n := num;
  
  var i := 9;
  while i >= 2
    invariant 1 <= i <= 9
    invariant n >= 1
    invariant mul >= 1
    invariant ans >= 0
    invariant mul <= 1000000000 // 10^9 to prevent overflow
    decreases i
  {
    while n % i == 0
      invariant n >= 1
      invariant mul >= 1
      invariant ans >= 0
      invariant mul <= 1000000000
      decreases n
    {
      n := n / i;
      if mul <= 214748364 && ans <= 2147483647 - mul * i {
        ans := mul * i + ans;
        if mul <= 100000000 {
          mul := mul * 10;
        } else {
          return 0; // overflow protection
        }
      } else {
        return 0; // overflow protection
      }
    }
    i := i - 1;
  }
  
  if n < 2 && ans <= 2147483647 {
    return ans;
  } else {
    return 0;
  }
}

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 0 <= result
{
  var f := new int[n + 1, n + 1];
  
  // Initialize array
  var row := 0;
  while row <= n
    invariant 0 <= row <= n + 1
    invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] >= 0
  {
    var col := 0;
    while col <= n
      invariant 0 <= col <= n + 1
      invariant forall c :: 0 <= c < col ==> f[row, c] >= 0
      invariant forall r, c :: 0 <= r < row && 0 <= c <= n ==> f[r, c] >= 0
    {
      f[row, col] := 0;
      col := col + 1;
    }
    row := row + 1;
  }
  
  var i := n - 1;
  while i >= 1
    invariant 0 <= i <= n - 1
    invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
    decreases i
  {
    var j := i + 1;
    while j <= n
      invariant i + 1 <= j <= n + 1
      invariant 1 <= i <= n - 1
      invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
    {
      if j - 1 >= 0 && j - 1 <= n {
        f[i, j] := j + f[i, j - 1];
      } else {
        f[i, j] := j;
      }
      
      var k := i;
      while k < j
        invariant i <= k <= j
        invariant 1 <= i <= n - 1
        invariant i + 1 <= j <= n
        invariant f[i, j] >= 0
        invariant forall r, c :: 0 <= r <= n && 0 <= c <= n ==> f[r, c] >= 0
      {
        var left_val := if k - 1 >= 0 && k - 1 <= n then f[i, k - 1] else 0;
        var right_val := if k + 1 >= 0 && k + 1 <= n then f[k + 1, j] else 0;
        var max_val := if left_val > right_val then left_val else right_val;
        var candidate := max_val + k;
        
        if candidate < f[i, j] {
          f[i, j] := candidate;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  return f[1, n];
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures result >= 0
{
  if n == 1 {
    return 9;
  }
  
  var mx := power10(n) - 1;
  var a := mx;
  
  while a > mx / 10
    invariant 0 <= a <= mx
    decreases a
  {
    var x := createPalindrome(a);
    var t := mx;
    
    while t * t >= x && t > 0
      invariant 0 <= t <= mx
      decreases t
    {
      if x % t == 0 {
        return x % 1337;
      }
      t := t - 1;
    }
    a := a - 1;
  }
  
  return 9;
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

method createPalindrome(a: int) returns (x: int)
  requires a >= 0
  ensures x >= 0
{
  x := a;
  var b := a;
  
  while b > 0
    invariant b >= 0
    invariant x >= 0
    decreases b
  {
    x := x * 10 + b % 10;
    b := b / 10;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := smallestFactorization_625(o);
  
  // Check if o1 is in valid range for getMoneyAmount_375
  if o1 < 1 || o1 > 200 {
    result := 0;
    return;
  }
  
  var o2 := getMoneyAmount_375(o1);
  
  // Check if o2 is in valid range for largestPalindrome_479
  if o2 < 1 || o2 > 8 {
    result := 0;
    return;
  }
  
  result := largestPalindrome_479(o2);
}
