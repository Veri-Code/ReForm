
method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures result >= 1
  ensures result > n
  decreases *
{
  var x := n + 1;
  while true
    invariant x > n
    invariant x >= 1
    decreases *
  {
    var y := x;
    var cnt := new int[10];
    var i := 0;
    while i < 10
      invariant 0 <= i <= 10
      invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
      cnt[i] := 0;
      i := i + 1;
    }
    
    while y > 0
      invariant y >= 0
      invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
      decreases y
    {
      var digit := y % 10;
      y := y / 10;
      if 0 <= digit < 10 {
        cnt[digit] := cnt[digit] + 1;
      }
    }
    
    var isBeautiful := true;
    i := 0;
    while i < 10 && isBeautiful
      invariant 0 <= i <= 10
      invariant isBeautiful ==> forall j :: 0 <= j < i ==> (cnt[j] == 0 || cnt[j] == j)
    {
      if cnt[i] != 0 && cnt[i] != i {
        isBeautiful := false;
      }
      i := i + 1;
    }
    
    if isBeautiful {
      return x;
    }
    x := x + 1;
  }
}

method power10(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures result >= 10
{
  result := 10;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant result >= 10
    decreases n - i
  {
    result := result * 10;
    i := i + 1;
  }
}

method reverseNumber(a: int) returns (result: int)
  requires a >= 0
  ensures result >= 0
{
  result := 0;
  var b := a;
  while b > 0
    invariant b >= 0
    invariant result >= 0
    decreases b
  {
    result := result * 10 + b % 10;
    b := b / 10;
  }
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 100000000
{
  if n == 1 {
    return 9;
  }
  
  var mx := power10(n);
  mx := mx - 1;
  var a := mx;
  
  while a > mx / 10
    invariant a >= 0
    invariant mx >= 9
    decreases a
  {
    var x := reverseNumber(a);
    var temp := a;
    while temp > 0
      invariant temp >= 0
      invariant x >= 0
      decreases temp
    {
      x := x * 10 + temp % 10;
      temp := temp / 10;
    }
    
    var t := mx;
    while t * t >= x && t > 0
      invariant t >= 0
      decreases t
    {
      if x % t == 0 {
        var res := x % 1337;
        if res == 0 {
          return 1337;
        } else {
          return res;
        }
      }
      t := t - 1;
    }
    a := a - 1;
  }
  return 9;
}

method isPrime(x: int) returns (result: bool)
  requires x >= 0
{
  if x < 2 {
    return false;
  }
  var v := 2;
  while v * v <= x
    invariant v >= 2
    invariant forall k :: 2 <= k < v ==> x % k != 0
    decreases x - v * v + 1
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  return true;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures result >= 1
  decreases *
{
  var current := n;
  while true
    invariant current >= n
    invariant current >= 1
    decreases *
  {
    var reversed := reverseNumber(current);
    if reversed == current {
      var prime := isPrime(current);
      if prime {
        return current;
      }
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 0 <= o <= 1000000
  ensures result >= 1
  decreases *
{
  var o1 := nextBeautifulNumber_2048(o);
  if o1 <= 8 {
    var o2 := largestPalindrome_479(o1);
    var o3 := primePalindrome_866(o2);
    result := o3;
  } else {
    result := 1;
  }
}
