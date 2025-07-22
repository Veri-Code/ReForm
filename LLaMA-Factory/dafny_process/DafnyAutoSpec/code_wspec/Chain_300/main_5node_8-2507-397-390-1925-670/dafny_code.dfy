
method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 2147483648
  decreases *
{
  var current := n;
  
  while true
    invariant current >= 2
    decreases *
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp := current;
    
    // Factor current and sum the prime factors
    while i * i <= temp && temp > 1
      invariant i >= 2
      invariant s >= 0
      invariant temp >= 1
      invariant temp <= current
      decreases temp - i + 1
    {
      while temp % i == 0 && temp > 1
        invariant temp >= 1
        invariant s >= 0
        decreases temp
      {
        temp := temp / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    // If temp > 1, it's a prime factor
    if temp > 1 {
      s := s + temp;
    }
    
    // If sum equals original, we found our answer
    if s == t {
      if t >= 1 && t <= 2147483648 {
        return t;
      } else {
        return 1;
      }
    }
    
    current := s;
    if current < 2 {
      current := 2;
    }
  }
}

method integerReplacement_397(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures 1 <= result <= 1000000000
  decreases *
{
  var current := n;
  var ans := 0;
  
  while current != 1
    invariant current >= 1
    invariant ans >= 0
    decreases *
  {
    if current % 2 == 0 {
      current := current / 2;
    } else if current != 3 && current % 4 == 3 {
      current := current + 1;
    } else {
      current := current - 1;
    }
    ans := ans + 1;
    if ans >= 1000000000 {
      return 1000000000;
    }
  }
  
  if ans == 0 {
    return 1;
  }
  if ans >= 1 && ans <= 1000000000 {
    return ans;
  } else {
    return 1;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 250
{
  if n == 1 {
    return 1;
  }
  
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant a1 >= 1
    invariant i >= 0
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
  
  if a1 > 250 {
    return 250;
  }
  if a1 >= 1 {
    return a1;
  } else {
    return 1;
  }
}

method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x
  ensures (result + 1) * (result + 1) > x
{
  if x == 0 {
    return 0;
  }
  if x == 1 {
    return 1;
  }
  
  var low := 0;
  var high := x;
  
  while low <= high
    invariant 0 <= low <= high + 1
    invariant high >= 0
    invariant low == 0 || (low - 1) * (low - 1) <= x
    invariant (high + 1) * (high + 1) > x
    decreases high - low
  {
    var mid := (low + high) / 2;
    var mid_squared := mid * mid;
    
    if mid_squared == x {
      return mid;
    } else if mid_squared < x {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  return high;
}

method countTriples_1925(n: int) returns (result: int)
  requires 1 <= n <= 250
  ensures 0 <= result <= 100000000
{
  var ans := 0;
  var a := 1;
  
  while a < n
    invariant 1 <= a <= n
    invariant 0 <= ans <= 100000000
  {
    var b := 1;
    while b < n
      invariant 1 <= b <= n
      invariant 0 <= ans <= 100000000
    {
      var x := a * a + b * b;
      var c := isqrt(x);
      if c <= n && c * c == x {
        ans := ans + 1;
        if ans >= 100000000 {
          return 100000000;
        }
      }
      b := b + 1;
    }
    a := a + 1;
  }
  
  return ans;
}

method maximumSwap_670(num: int) returns (result: int)
  requires 0 <= num <= 100000000
  ensures result >= 0
{
  // Convert number to array of digits
  var digits: seq<int> := [];
  var temp := num;
  
  if temp == 0 {
    return 0;
  }
  
  while temp > 0
    invariant temp >= 0
    invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
    decreases temp
  {
    var digit := temp % 10;
    digits := [digit] + digits;
    temp := temp / 10;
  }
  
  var n := |digits|;
  if n == 0 {
    return 0;
  }
  
  // Create array d where d[i] points to the rightmost largest digit from position i onwards
  var d: seq<int> := seq(n, i => i);
  var i := n - 2;
  
  while i >= 0
    invariant -1 <= i < n
    invariant |d| == n
    invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
  {
    if i + 1 < n && digits[i] <= digits[d[i + 1]] {
      d := d[i := d[i + 1]];
    }
    i := i - 1;
  }
  
  // Find first position where we can make a beneficial swap
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |digits| == n
    invariant |d| == n
    invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
  {
    if i < n && d[i] < n && digits[i] < digits[d[i]] {
      // Perform the swap
      var temp_digit := digits[i];
      digits := digits[i := digits[d[i]]];
      digits := digits[d[i] := temp_digit];
      break;
    }
    i := i + 1;
  }
  
  // Convert back to integer
  result := 0;
  i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant result >= 0
    invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
  {
    result := result * 10 + digits[i];
    i := i + 1;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result >= 0
  decreases *
{
  var o1 := smallestValue_2507(o);
  var o2 := integerReplacement_397(o1);
  var o3 := lastRemaining_390(o2);
  var o4 := countTriples_1925(o3);
  var o5 := maximumSwap_670(o4);
  return o5;
}
