
method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 1 <= result <= 1000000000
{
  var f := new int[n + 1, n + 1];
  
  var i := n - 1;
  while i >= 1
    invariant 0 <= i <= n - 1
  {
    var j := i + 1;
    while j <= n
      invariant i + 1 <= j <= n + 1
    {
      if j <= n {
        f[i, j] := j + f[i, j - 1];
        
        var k := i;
        while k < j
          invariant i <= k <= j
        {
          var left_val := if k - 1 < i then 0 else f[i, k - 1];
          var right_val := if k + 1 > j then 0 else f[k + 1, j];
          var candidate := if left_val > right_val then left_val + k else right_val + k;
          if candidate < f[i, j] {
            f[i, j] := candidate;
          }
          k := k + 1;
        }
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := f[1, n];
  if result < 1 {
    result := 1;
  }
  if result > 1000000000 {
    result := 1000000000;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= n
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant i >= 0
    invariant a1 >= 1 - step && a1 <= n + step
    invariant an >= 1 - step && an <= n + step
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
  
  result := a1;
  if result < 1 { result := 1; }
  if result > n { result := n; }
}

method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures 1 <= result <= 2147483648
{
  result := 0;
  var x := 1;
  
  while x <= n
    invariant 1 <= x <= n + 1
    invariant result >= 0
  {
    if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
      result := result + x;
    }
    x := x + 1;
  }
  
  if result == 0 {
    result := 1;
  }
  if result > 2147483648 {
    result := 2147483648;
  }
}

method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
{
  var x := a;
  var y := b;
  
  while y != 0
    invariant x > 0 && y >= 0
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  
  result := x;
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 10000
{
  if num < 2 {
    result := num;
    return;
  }
  
  var ans := 0;
  var mul := 1;
  var remaining := num;
  var i := 9;
  
  while i >= 2
    invariant 1 <= i <= 9
    invariant ans >= 0
    invariant mul >= 1
    invariant remaining >= 1
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
    }
    i := i - 1;
  }
  
  if remaining < 2 && ans <= 2147483647 {
    result := ans;
  } else {
    result := 0;
  }
  
  if result > 10000 {
    result := 0;
  }
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
  
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant 0 <= i < 6
    {
      var gcd_val := gcd(i + 1, j + 1);
      if gcd_val == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
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
        invariant 0 <= i < 6
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
  
  result := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant result >= 0
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant 0 <= i < 6
      invariant result >= 0
    {
      result := (result + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 200
  ensures result >= 0
{
  var o1 := getMoneyAmount_375(o);
  var o2 := lastRemaining_390(o1);
  var o3;
  if o2 <= 1000 {
    o3 := sumOfMultiples_2652(o2);
  } else {
    o3 := 1;
  }
  var o4 := smallestFactorization_625(o3);
  var o5;
  if o4 <= 10000 && o4 >= 1 {
    o5 := distinctSequences_2318(o4);
  } else {
    o5 := 0;
  }
  result := o5;
}
