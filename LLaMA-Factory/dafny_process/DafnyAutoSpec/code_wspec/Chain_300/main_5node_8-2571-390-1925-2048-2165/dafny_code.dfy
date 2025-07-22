
method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 1000000000
{
  var ans := 0;
  var cnt := 0;
  var num := n;
  
  while num > 0
    invariant ans >= 0
    invariant cnt >= 0
    invariant num >= 0
  {
    if num % 2 == 1 {
      cnt := cnt + 1;
    } else if cnt > 0 {
      ans := ans + 1;
      cnt := if cnt == 1 then 0 else 1;
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
  if result > 1000000000 {
    result := 1000000000;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 250
{
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
  
  result := a1;
  if result < 1 {
    result := 1;
  } else if result > 250 {
    result := 250;
  }
}

method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x
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
  
  result := r;
}

method countTriples_1925(n: int) returns (result: int)
  requires 1 <= n <= 250
  ensures 0 <= result <= 1000000
{
  var ans := 0;
  var a := 1;
  
  while a < n
    invariant 1 <= a <= n
    invariant ans >= 0
    invariant ans <= 1000000
  {
    var b := 1;
    while b < n
      invariant 1 <= b <= n
      invariant ans >= 0
      invariant ans <= 1000000
    {
      var x := a * a + b * b;
      var c := isqrt(x);
      if c <= n && c * c == x {
        ans := ans + 1;
        if ans > 1000000 {
          ans := 1000000;
        }
      }
      b := b + 1;
    }
    a := a + 1;
  }
  
  result := ans;
}

method countDigits(x: int) returns (digits: array<int>)
  requires x >= 0
  ensures digits.Length == 10
  ensures forall i :: 0 <= i < 10 ==> digits[i] >= 0
{
  digits := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant forall j :: 0 <= j < i ==> digits[j] >= 0
  {
    digits[i] := 0;
    i := i + 1;
  }
  
  var num := x;
  if num == 0 {
    digits[0] := 1;
  } else {
    while num > 0
      invariant num >= 0
      invariant forall j :: 0 <= j < 10 ==> digits[j] >= 0
    {
      var digit := num % 10;
      digits[digit] := digits[digit] + 1;
      num := num / 10;
    }
  }
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x > 0
{
  var digits := countDigits(x);
  beautiful := true;
  var i := 0;
  
  while i < 10 && beautiful
    invariant 0 <= i <= 10
  {
    if digits[i] > 0 && digits[i] != i {
      beautiful := false;
    }
    i := i + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures -1000000000000000 <= result <= 1000000000000000
{
  var x := n + 1;
  var found := false;
  var iterations := 0;
  
  while !found && iterations < 10000000
    invariant x >= n + 1
    invariant iterations >= 0
  {
    var beautiful := isBeautiful(x);
    if beautiful {
      found := true;
    } else {
      x := x + 1;
      iterations := iterations + 1;
    }
  }
  
  result := x;
  if result < -1000000000000000 {
    result := -1000000000000000;
  } else if result > 1000000000000000 {
    result := 1000000000000000;
  }
}

method abs(x: int) returns (result: int)
  ensures result >= 0
  ensures result == x || result == -x
{
  if x >= 0 {
    result := x;
  } else {
    result := -x;
  }
}

method smallestNumber_2165(num: int) returns (result: int)
  requires -1000000000000000 <= num <= 1000000000000000
{
  var neg := num < 0;
  var absNum := abs(num);
  var cnt := new int[10];
  var i := 0;
  
  while i < 10
    invariant 0 <= i <= 10
    invariant forall j :: 0 <= j < i ==> cnt[j] >= 0
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var temp := absNum;
  if temp == 0 {
    cnt[0] := 1;
  } else {
    while temp > 0
      invariant temp >= 0
      invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
    {
      var digit := temp % 10;
      cnt[digit] := cnt[digit] + 1;
      temp := temp / 10;
    }
  }
  
  var ans := 0;
  
  if neg {
    i := 9;
    while i >= 0
      invariant -1 <= i <= 9
    {
      var j := 0;
      while j < cnt[i]
        invariant 0 <= j <= cnt[i]
        invariant cnt[i] >= 0
      {
        ans := ans * 10 + i;
        j := j + 1;
      }
      i := i - 1;
    }
    result := -ans;
  } else {
    if cnt[0] > 0 {
      i := 1;
      while i < 10
        invariant 1 <= i <= 10
      {
        if cnt[i] > 0 {
          ans := i;
          cnt[i] := cnt[i] - 1;
          break;
        }
        i := i + 1;
      }
    }
    
    i := 0;
    while i < 10
      invariant 0 <= i <= 10
    {
      var j := 0;
      while j < cnt[i]
        invariant 0 <= j <= cnt[i]
        invariant cnt[i] >= 0
      {
        ans := ans * 10 + i;
        j := j + 1;
      }
      i := i + 1;
    }
    result := ans;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 100000
  ensures true
{
  var o1 := minOperations_2571(o);
  var o2 := lastRemaining_390(o1);
  var o3 := countTriples_1925(o2);
  var o4 := nextBeautifulNumber_2048(o3);
  var o5 := smallestNumber_2165(o4);
  result := o5;
}
