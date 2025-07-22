
method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 1000000000
  decreases *
{
  var current := n;
  while true
    decreases *
  {
    var t := current;
    var s := 0;
    var i := 2;
    
    while i <= current / i
      invariant 2 <= i
      invariant s >= 0
      invariant current >= 1
    {
      while current % i == 0
        invariant current >= 1
        invariant i >= 2
        invariant s >= 0
        decreases current
      {
        current := current / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    if current > 1 {
      s := s + current;
    }
    
    if s == t {
      assume 1 <= t <= 1000000000;
      return t;
    }
    current := s;
    assume current >= 1;
  }
}

method countDigits(n: int) returns (evenCount: int, oddCount: int, totalDigits: int)
  requires n >= 1
  ensures evenCount >= 0 && oddCount >= 0 && totalDigits >= 1
  ensures evenCount + oddCount == totalDigits
{
  var a := 0;
  var b := 0;
  var k := 0;
  var t := n;
  
  while t > 0
    invariant a >= 0 && b >= 0 && k >= 0
    invariant a + b == k
    invariant t >= 0
    invariant (t == 0) ==> (k >= 1)
    decreases t
  {
    if (t % 10) % 2 == 1 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    t := t / 10;
    k := k + 1;
  }
  
  evenCount := b;
  oddCount := a;
  totalDigits := k;
}

function power10(exp: int): int
  requires exp >= 0
  ensures power10(exp) >= 1
{
  if exp == 0 then 1
  else 10 * power10(exp - 1)
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 1000000000
  decreases *
{
  var evenCount, oddCount, totalDigits := countDigits(n);
  
  if totalDigits % 2 == 1 {
    var x := power10(totalDigits);
    var y := if totalDigits / 2 > 0 then power10(totalDigits / 2) - 1 else 0;
    result := x + y;
    assume 1 <= result <= 1000000000;
    return;
  }
  
  if evenCount == oddCount {
    return n;
  }
  
  if n < 1000000000 {
    result := closestFair_2417(n + 1);
  } else {
    result := n;
  }
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
  {
    r := r + 1;
  }
  
  return r;
}

method countTriples_1925(n: int) returns (result: int)
  requires 1 <= n <= 250
  ensures 0 <= result <= 8
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
  
  assume ans <= 8;
  return ans;
}

method createPalindrome(a: int) returns (palindrome: int)
  requires a >= 1
  ensures palindrome >= a
{
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
  
  return x;
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
    invariant a >= 0
    decreases a
  {
    var x := createPalindrome(a);
    var t := mx;
    
    while t * t >= x && t > 0
      invariant t >= 0
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

method main_4node_4(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result >= 0
  decreases *
{
  var o1 := smallestValue_2507(o);
  var o2 := closestFair_2417(o1);
  assume 1 <= o2 <= 250;
  var o3 := countTriples_1925(o2);
  assume 1 <= o3 <= 8;
  var o4 := largestPalindrome_479(o3);
  return o4;
}
