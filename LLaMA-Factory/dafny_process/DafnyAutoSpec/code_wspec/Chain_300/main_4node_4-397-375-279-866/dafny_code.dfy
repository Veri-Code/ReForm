
method integerReplacement_397(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures 1 <= result <= 200
{
  var current := n;
  var ans := 0;
  
  while current != 1 && ans < 200
    invariant current >= 1
    invariant ans >= 0
    invariant ans <= 200
    decreases if current == 1 then 0 else 200 - ans
  {
    if current % 2 == 0 {
      current := current / 2;
    } else if current != 3 && current % 4 == 3 {
      current := current + 1;
    } else {
      current := current - 1;
    }
    ans := ans + 1;
  }
  
  if current == 1 {
    result := ans;
  } else {
    result := 200;
  }
  
  // Ensure result is at least 1
  if result < 1 {
    result := 1;
  }
}

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 1 <= result <= 10000
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
  
  // Main DP computation
  i := n - 1;
  while i >= 1
    invariant 0 <= i <= n
  {
    var j := i + 1;
    while j <= n
      invariant i + 1 <= j <= n + 1
    {
      if j > 0 {
        f[i, j] := j + f[i, j - 1];
        
        var k := i;
        while k < j
          invariant i <= k <= j
        {
          var left_cost := if k - 1 >= 0 then f[i, k - 1] else 0;
          var right_cost := if k + 1 <= n then f[k + 1, j] else 0;
          var max_cost := if left_cost > right_cost then left_cost else right_cost;
          var total_cost := max_cost + k;
          
          if total_cost < f[i, j] {
            f[i, j] := total_cost;
          }
          
          k := k + 1;
        }
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := if f[1, n] >= 1 then f[1, n] else 1;
  if result > 10000 {
    result := 10000;
  }
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 100000000
{
  var m := 1;
  while m * m <= n
    invariant m >= 1
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
      f[i, j] := 100000000;
      j := j + 1;
    }
    i := i + 1;
  }
  
  f[0, 0] := 0;
  
  // Main DP computation
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
  
  result := if f[m, n] >= 1 then f[m, n] else 1;
  if result > 100000000 {
    result := 100000000;
  }
}

method is_prime(x: int) returns (result: bool)
  requires x >= 1
{
  if x < 2 {
    result := false;
    return;
  }
  
  var v := 2;
  while v * v <= x
    invariant 2 <= v
    invariant forall k :: 2 <= k < v ==> x % k != 0
    decreases x - v * v + 1
  {
    if x % v == 0 {
      result := false;
      return;
    }
    v := v + 1;
  }
  
  result := true;
}

method reverse(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  var current := x;
  var res := 0;
  
  while current > 0
    invariant current >= 0
    invariant res >= 0
    decreases current
  {
    res := res * 10 + current % 10;
    current := current / 10;
  }
  
  result := res;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures result >= 1
{
  var current := n;
  var iterations := 0;
  
  while iterations < 200000000
    invariant current >= 1
    invariant iterations >= 0
  {
    var rev := reverse(current);
    if rev == current {
      var prime := is_prime(current);
      if prime {
        result := current;
        return;
      }
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
    iterations := iterations + 1;
  }
  
  result := 1;
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 1
{
  var o1 := integerReplacement_397(o);
  var o2 := getMoneyAmount_375(o1);
  var o3 := numSquares_279(o2);
  var o4 := primePalindrome_866(o3);
  result := o4;
}
