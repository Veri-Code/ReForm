
method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 250
{
  var ans := 0;
  var cnt := 0;
  var num := n;
  
  while num > 0
    invariant ans >= 0
    invariant cnt >= 0
    invariant num >= 0
    decreases num
  {
    if num % 2 == 1 {
      cnt := cnt + 1;
    } else if cnt > 0 {
      ans := ans + 1;
      if cnt == 1 {
        cnt := 0;
      } else {
        cnt := 1;
      }
    }
    num := num / 2;
  }
  
  if cnt == 1 {
    ans := ans + 1;
  } else if cnt > 1 {
    ans := ans + 2;
  }
  
  result := ans;
  if result == 0 {
    result := 1;
  }
  
  if result > 250 {
    result := 250;
  }
}

method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x
  ensures x < (result + 1) * (result + 1)
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
    invariant low <= x + 1
    invariant high >= 0
    invariant (low - 1) * (low - 1) <= x
    invariant x < (high + 1) * (high + 1)
    decreases high - low
  {
    var mid := (low + high) / 2;
    if mid * mid == x {
      return mid;
    } else if mid * mid < x {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  result := high;
}

method countTriples_1925(n: int) returns (result: int)
  requires 1 <= n <= 250
  ensures 2 <= result <= 100000
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
  
  result := if ans >= 2 then ans else 2;
  if result > 100000 {
    result := 100000;
  }
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures result >= 2
{
  var current := n;
  var iterations := 0;
  
  while iterations < 1000
    invariant current >= 2
    invariant iterations >= 0
    decreases 1000 - iterations
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp := current;
    
    while i * i <= temp
      invariant i >= 2
      invariant s >= 0
      invariant temp >= 1
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
    
    if temp > 1 {
      s := s + temp;
    }
    
    if s == t {
      return t;
    }
    
    current := if s >= 2 then s else 2;
    iterations := iterations + 1;
  }
  
  result := current;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 100000
  ensures result >= 2
{
  var o1 := minOperations_2571(o);
  var o2 := countTriples_1925(o1);
  var o3 := smallestValue_2507(o2);
  result := o3;
}
