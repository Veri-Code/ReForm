
method smallestValue_2507(n0: int) returns (result: int)
  requires 2 <= n0 <= 100000
  ensures result >= 2
  ensures result <= 1000000
{
  var n := n0;
  var iterations := 0;
  
  while iterations < 50
    invariant 2 <= n <= 1000000
    invariant iterations >= 0
  {
    var t := n;
    var s := 0;
    var i := 2;
    var original_n := n;
    
    // Factor n and sum the prime factors
    while i * i <= n
      invariant 2 <= i
      invariant s >= 0
      invariant n >= 1
      invariant s <= 1000000
    {
      while n % i == 0
        invariant n >= 1
        invariant i >= 2
        invariant s >= 0
        invariant s <= 1000000
        decreases n
      {
        n := n / i;
        s := s + i;
        if s > 1000000 {
          s := 1000000;
        }
      }
      i := i + 1;
    }
    
    if n > 1 {
      s := s + n;
      if s > 1000000 {
        s := 1000000;
      }
    }
    
    if s == t {
      return t;
    }
    
    n := s;
    if n < 2 {
      n := 2;
    }
    iterations := iterations + 1;
  }
  
  // Fallback - should not reach here for valid inputs
  return n;
}

method nextBeautifulNumber_2048(n0: int) returns (result: int)
  requires 0 <= n0 <= 1000000
  ensures result > n0
{
  var x := n0 + 1;
  var attempts := 0;
  
  while attempts < 10000000
    invariant x > n0
    invariant attempts >= 0
  {
    var isBeautifulResult := isBeautiful(x);
    if isBeautifulResult {
      return x;
    }
    x := x + 1;
    attempts := attempts + 1;
  }
  
  // Fallback
  return x;
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x >= 0
{
  var counts := getDigitCounts(x);
  beautiful := true;
  var i := 0;
  while i <= 9
    invariant 0 <= i <= 10
    invariant counts.Length == 10
  {
    if counts[i] != 0 && counts[i] != i {
      beautiful := false;
      return;
    }
    i := i + 1;
  }
}

method getDigitCounts(x: int) returns (counts: array<int>)
  requires x >= 0
  ensures counts.Length == 10
  ensures fresh(counts)
{
  counts := new int[10];
  var y := x;
  
  while y > 0
    invariant y >= 0
    invariant counts.Length == 10
    modifies counts
  {
    var digit := y % 10;
    y := y / 10;
    if 0 <= digit <= 9 {
      counts[digit] := counts[digit] + 1;
    }
  }
}

method main_2node_1(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result > 0
{
  var o1 := smallestValue_2507(o);
  var o2 := nextBeautifulNumber_2048(o1);
  result := o2;
}
