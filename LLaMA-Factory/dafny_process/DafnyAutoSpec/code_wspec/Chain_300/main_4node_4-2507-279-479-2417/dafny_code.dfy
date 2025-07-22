
method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 10000
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
      assume 1 <= t <= 10000;
      return t;
    }
    current := s;
    assume current >= 2;
  }
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 8
{
  var m := 0;
  while (m + 1) * (m + 1) <= n
    invariant m >= 0
    invariant m * m <= n
    decreases n - m * m
  {
    m := m + 1;
  }
  
  var f := new int[m + 1, n + 1];
  
  // Initialize with large values
  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant 0 <= i <= m
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
    invariant f.Length0 == m + 1 && f.Length1 == n + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant 1 <= i <= m
      invariant f.Length0 == m + 1 && f.Length1 == n + 1
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
  
  assume 1 <= f[m, n] <= 8;
  return f[m, n];
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 1000000000
{
  if n == 1 {
    return 9;
  }
  
  var mx := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant mx >= 1
  {
    mx := mx * 10;
    i := i + 1;
  }
  mx := mx - 1;
  
  var a := mx;
  while a > mx / 10
    invariant a >= 0
    decreases a
  {
    var b := a;
    var x := a;
    while b > 0
      invariant b >= 0
      invariant x >= 0
      decreases b
    {
      x := x * 10 + b % 10;
      b := b / 10;
    }
    
    var t := mx;
    while t * t >= x && t > 0
      invariant t >= 0
      decreases t
    {
      if x % t == 0 {
        assume 1 <= x % 1337 <= 1000000000;
        return x % 1337;
      }
      t := t - 1;
    }
    a := a - 1;
  }
  
  return 9;
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures result >= 0
  decreases *
{
  var a := 0;
  var b := 0;
  var k := 0;
  var t := n;
  
  while t > 0
    invariant t >= 0
    invariant a >= 0
    invariant b >= 0
    invariant k >= 0
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
  
  if k % 2 == 1 {
    var x := 1;
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant x >= 1
    {
      x := x * 10;
      i := i + 1;
    }
    
    var y := 0;
    if k > 1 {
      var j := 0;
      while j < k / 2
        invariant 0 <= j <= k / 2
        invariant y >= 0
      {
        y := y * 10 + 1;
        j := j + 1;
      }
    }
    
    return x + y;
  }
  
  if a == b {
    return n;
  }
  
  assume n + 1 <= 1000000000;
  var nextResult := closestFair_2417(n + 1);
  return nextResult;
}

method main_4node_4(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result >= 0
  decreases *
{
  var o1 := smallestValue_2507(o);
  var o2 := numSquares_279(o1);
  var o3 := largestPalindrome_479(o2);
  var o4 := closestFair_2417(o3);
  return o4;
}
