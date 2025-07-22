
method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 250
{
  var mx := power10(n) - 1;
  var a := mx;
  
  while a > mx / 10
    invariant mx / 10 <= a <= mx
    invariant mx == power10(n) - 1
    decreases a
  {
    // Create palindrome from a
    var b := a;
    var x := a;
    while b > 0
      invariant b >= 0
      invariant x >= a
      decreases b
    {
      x := x * 10 + b % 10;
      b := b / 10;
    }
    
    // Check if x can be expressed as product of two numbers <= mx
    var t := mx;
    while t * t >= x && t > 0
      invariant t >= 0
      invariant t <= mx
      decreases t
    {
      if x % t == 0 {
        var quotient := x / t;
        if quotient <= mx {
          var mod_result := x % 1337;
          if mod_result == 0 {
            return 250;
          } else if mod_result <= 250 {
            return mod_result;
          } else {
            return mod_result % 250 + 1;
          }
        }
      }
      t := t - 1;
    }
    
    a := a - 1;
  }
  
  return 9;
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
    decreases n - a
  {
    var b := 1;
    while b < n
      invariant 1 <= b <= n
      invariant ans >= 0
      decreases n - b
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

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 8
  ensures result >= 0
{
  var o1 := largestPalindrome_479(o);
  var o2 := countTriples_1925(o1);
  return o2;
}

// Helper function to compute 10^n
function power10(n: int): int
  requires 0 <= n <= 8
  ensures power10(n) >= 1
  ensures n >= 1 ==> power10(n) >= 10
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

// Helper function to compute integer square root
method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x
  ensures (result + 1) * (result + 1) > x
{
  if x == 0 {
    return 0;
  }
  
  var r := x;
  while r * r > x
    invariant r > 0
    decreases r
  {
    r := (r + x / r) / 2;
  }
  
  // Ensure we have the largest integer whose square is <= x
  while (r + 1) * (r + 1) <= x
    invariant r >= 0
    invariant r * r <= x
    decreases x - r * r
  {
    r := r + 1;
  }
  
  return r;
}
