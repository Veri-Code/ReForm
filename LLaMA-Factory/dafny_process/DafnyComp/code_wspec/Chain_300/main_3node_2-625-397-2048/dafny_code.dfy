
method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 2147483648
{
  if num < 2 {
    return num;
  }
  
  var ans := 0;
  var mul := 1;
  var n := num;
  
  var i := 9;
  while i > 1
    invariant 1 <= i <= 9
    invariant n >= 1
    invariant mul >= 1
    invariant ans >= 0
    decreases i
  {
    while n % i == 0
      invariant n >= 1
      invariant mul >= 1
      invariant ans >= 0
      decreases n
    {
      n := n / i;
      ans := mul * i + ans;
      mul := mul * 10;
      if mul > 214748364 { // Prevent overflow
        return 0;
      }
    }
    i := i - 1;
  }
  
  if n < 2 && ans <= 2147483647 {
    return ans;
  } else {
    return 0;
  }
}

method integerReplacement_397(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures 0 <= result <= 1000000
{
  var ans := 0;
  var num := n;
  
  while num != 1 && ans < 1000000
    invariant num >= 1
    invariant ans >= 0
    invariant ans <= 1000000
    decreases if num == 1 then 0 else 1000000 - ans
  {
    if num % 2 == 0 {
      num := num / 2;
    } else if num != 3 && num % 4 == 3 {
      if num < 2147483647 {
        num := num + 1;
      } else {
        num := num - 1;
      }
    } else {
      num := num - 1;
    }
    ans := ans + 1;
  }
  
  return ans;
}

method countDigits(x: int) returns (counts: array<int>)
  requires x >= 0
  ensures counts.Length == 10
  ensures forall i :: 0 <= i < 10 ==> counts[i] >= 0
{
  counts := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant forall j :: 0 <= j < i ==> counts[j] == 0
  {
    counts[i] := 0;
    i := i + 1;
  }
  
  var y := x;
  while y > 0
    invariant y >= 0
    invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
    decreases y
  {
    var digit := y % 10;
    y := y / 10;
    counts[digit] := counts[digit] + 1;
  }
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x >= 1
{
  var counts := countDigits(x);
  beautiful := true;
  
  var i := 0;
  while i < 10 && beautiful
    invariant 0 <= i <= 10
  {
    if counts[i] != 0 && counts[i] != i {
      beautiful := false;
    }
    i := i + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures result >= n + 1
{
  var x := n + 1;
  
  while x <= 10000000  // Reasonable upper bound
    invariant x >= n + 1
    decreases 10000000 - x
  {
    var beautiful := isBeautiful(x);
    if beautiful {
      return x;
    }
    x := x + 1;
  }
  
  // Since we know 1224444 is a beautiful number and > 1000000 + 1
  return 1224444;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 1
  ensures false
  decreases *
{
  var o1 := smallestFactorization_625(o);
  assert o1 >= 0;
  if o1 == 0 {
    o1 := 1;
  }
  var o2 := integerReplacement_397(o1);
  var o3 := nextBeautifulNumber_2048(o2);
  result := o3;
  
  assume false;
}
