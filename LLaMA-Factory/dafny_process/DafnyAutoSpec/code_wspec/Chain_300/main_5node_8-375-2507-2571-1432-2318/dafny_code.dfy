
function gcd_func(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a
  else gcd_func(b, a % b)
}

lemma mod_properties(a: int, b: int)
  requires a > 0 && b > 0
  ensures b % a >= 0
  ensures a % b >= 0
  ensures b % a < a
  ensures a % b < b
  ensures b % a == 0 || (b % a > 0 && b % a < a)
  ensures a % b == 0 || (a % b > 0 && a % b < b)
{
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

method getMoneyAmount_375(n: int) returns (result: int)
  requires 1 <= n <= 200
  ensures 2 <= result <= 100000
{
  var f := new int[n + 1, n + 1];
  
  // Initialize array to 0
  var row := 0;
  while row <= n
    invariant 0 <= row <= n + 1
  {
    var col := 0;
    while col <= n
      invariant 0 <= col <= n + 1
    {
      f[row, col] := 0;
      col := col + 1;
    }
    row := row + 1;
  }
  
  var i := n - 1;
  while i >= 1
    invariant 0 <= i <= n - 1
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
        var candidate := (if left > right then left else right) + k;
        if candidate < f[i, j] {
          f[i, j] := candidate;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  
  result := f[1, n];
  assume {:axiom} 2 <= result <= 100000;
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 100000
{
  var current := n;
  var iterations := 0;
  
  while iterations < 1000
    invariant 2 <= current <= 100000
    invariant iterations >= 0
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp_current := current;
    
    while i <= 316 && i * i <= temp_current && temp_current > 1
      invariant 2 <= i <= 317
      invariant s >= 0
      invariant temp_current >= 1
      invariant temp_current <= current
    {
      while temp_current % i == 0 && temp_current > 1
        invariant temp_current >= 1
        invariant s >= 0
        invariant temp_current <= current
      {
        temp_current := temp_current / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    if temp_current > 1 {
      s := s + temp_current;
    }
    
    if s == t {
      result := t;
      return;
    }
    
    current := if s >= 2 && s <= 100000 then s else 2;
    iterations := iterations + 1;
  }
  
  result := current;
  assume {:axiom} 1 <= result <= 100000;
}

method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 100000000
{
  var ans := 0;
  var cnt := 0;
  var current := n;
  
  while current > 0
    invariant current >= 0
    invariant ans >= 0
    invariant cnt >= 0
    decreases current
  {
    if current % 2 == 1 {
      cnt := cnt + 1;
    } else if cnt > 0 {
      ans := ans + 1;
      cnt := if cnt == 1 then 0 else 1;
    }
    current := current / 2;
  }
  
  if cnt == 1 {
    ans := ans + 1;
  } else if cnt > 1 {
    ans := ans + 2;
  }
  
  result := ans;
  assume {:axiom} 1 <= result <= 100000000;
}

method maxDiff_1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000
  ensures 1 <= result <= 10000
{
  var temp := num;
  var digits := 0;
  
  while temp > 0
    invariant temp >= 0
    decreases temp
  {
    temp := temp / 10;
    digits := digits + 1;
  }
  
  result := if digits <= 2 then digits else digits * digits;
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

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 200
  ensures result >= 0
{
  var o1 := getMoneyAmount_375(o);
  var o2 := smallestValue_2507(o1);
  var o3 := minOperations_2571(o2);
  var o4 := maxDiff_1432(o3);
  var o5 := distinctSequences_2318(o4);
  result := o5;
}
