
method isPrime(x: int) returns (result: bool)
  requires x >= 0
  ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
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
  
  // Need to prove that no divisors exist between v and x
  assert forall k :: 2 <= k < v ==> x % k != 0;
  assert v * v > x;
  
  // For any k where v <= k < x, if k divides x, then x/k < v
  // But x/k >= 2 (since k < x and k >= v >= 2), so x/k would be a divisor < v
  // This contradicts our invariant
  assert forall k :: v <= k < x ==> x % k != 0 by {
    forall k | v <= k < x
      ensures x % k != 0
    {
      if x % k == 0 {
        var quotient := x / k;
        assert quotient >= 2;
        assert quotient < v;
        assert x % quotient == 0;
        assert false;
      }
    }
  }
  
  return true;
}

method reverse(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  var res := 0;
  var temp := x;
  while temp > 0
    invariant temp >= 0
    invariant res >= 0
    decreases temp
  {
    res := res * 10 + temp % 10;
    temp := temp / 10;
  }
  return res;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures 2 <= result <= 100000000
  ensures result >= n
  decreases *
{
  var current := n;
  
  while true
    invariant current >= n
    invariant current >= 1
    invariant current <= 100000000
    decreases *
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
    } else {
      if current < 100000000 {
        current := current + 1;
      } else {
        return current;
      }
    }
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
  return x;
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 2 <= result <= 100000
  decreases *
{
  var current := n;
  
  while true
    invariant 2 <= current <= 100000
    decreases *
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp := current;
    
    while i <= temp / i
      invariant 2 <= i
      invariant temp >= 1
      invariant s >= 0
      decreases temp - i * i + 1
    {
      while temp % i == 0
        invariant temp >= 1
        invariant s >= 0
        invariant i >= 2
        decreases temp
      {
        temp := temp / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    if temp > 1 {
      s := s + temp;
    }
    
    if s == 0 {
      s := current;
    }
    
    if s == t {
      return t;
    }
    current := s;
    if s < 2 {
      current := 2;
    }
    if s > 100000 {
      current := 100000;
    }
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 1000000007
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize dp array
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
  
  // Fill base case
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
  
  // Fill DP table
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
          dp[k, i, j] := 0;
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
            invariant dp[k, i, j] >= 0
            invariant dp[k, i, j] < mod
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
  
  // Sum results
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant ans >= 0
    invariant ans < mod
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant ans >= 0
      invariant ans < mod
    {
      ans := (ans + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  if ans == 0 {
    return 1;
  }
  return ans;
}

method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x < (result + 1) * (result + 1)
{
  if x == 0 {
    return 0;
  }
  
  var r := x;
  while r * r > x
    invariant r >= 0
    decreases r
  {
    r := (r + x / r) / 2;
  }
  
  while (r + 1) * (r + 1) <= x
    invariant r >= 0
    invariant r * r <= x
    decreases x - r * r
  {
    r := r + 1;
  }
  
  return r;
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
  
  return ans;
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures result >= 0
  decreases *
{
  var o1 := primePalindrome_866(o);
  
  var bounded_o1 := if o1 <= 100000 then o1 else 100000;
  var o2 := smallestValue_2507(bounded_o1);
  
  var bounded_o2 := if o2 <= 10000 then o2 else 10000;
  var o3 := distinctSequences_2318(bounded_o2);
  
  var bounded_o3 := if o3 <= 250 then o3 else 250;
  var o4 := countTriples_1925(bounded_o3);
  return o4;
}
