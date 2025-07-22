
method countTriples_1925(n: int) returns (ans: int)
  requires 1 <= n <= 250
  ensures 0 <= ans <= 1000000
{
  ans := 0;
  var a := 1;
  while a < n
    invariant 1 <= a <= n
    invariant 0 <= ans <= (a - 1) * (n - 1)
  {
    var b := 1;
    while b < n
      invariant 1 <= b <= n
      invariant 0 <= ans <= (a - 1) * (n - 1) + (b - 1)
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
}

method isqrt(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
  ensures result * result <= x < (result + 1) * (result + 1)
{
  if x == 0 {
    return 0;
  }
  
  result := 1;
  while (result + 1) * (result + 1) <= x
    invariant result >= 0
    invariant result * result <= x
  {
    result := result + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures 1 <= result
{
  var x := n + 1;
  while x <= 1000000000
    invariant x >= n + 1
    invariant x <= 1000000001
    decreases 1000000001 - x
  {
    var beautiful := isBeautiful(x);
    if beautiful {
      return x;
    }
    x := x + 1;
  }
  result := 1000000001;
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x >= 1
{
  var y := x;
  var cnt := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  while y > 0
    invariant y >= 0
    decreases y
  {
    var digit := y % 10;
    y := y / 10;
    if digit < 10 {
      cnt[digit] := cnt[digit] + 1;
    }
  }
  
  beautiful := true;
  i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    if cnt[i] != 0 && i != cnt[i] {
      beautiful := false;
      break;
    }
    i := i + 1;
  }
}

method sumOfMultiples_2652(n: int) returns (sum: int)
  requires 1 <= n <= 1000
  ensures 1 <= sum <= 100000000
{
  sum := 0;
  var x := 1;
  while x <= n
    invariant 1 <= x <= n + 1
    invariant 0 <= sum <= x * n
  {
    if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
      sum := sum + x;
    }
    x := x + 1;
  }
  if sum == 0 {
    sum := 1;
  }
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures 1 <= result
{
  var current := n;
  while current <= 100000000
    invariant current >= n
    invariant current <= 100000001
    decreases 100000001 - current
  {
    var isPalin := isPalindrome(current);
    var isPrim := isPrime(current);
    if isPalin && isPrim {
      return current;
    }
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
  }
  result := 100000001;
}

method isPrime(x: int) returns (prime: bool)
  requires x >= 1
{
  if x < 2 {
    return false;
  }
  if x == 2 {
    return true;
  }
  
  var v := 2;
  while v * v <= x
    invariant 2 <= v
    invariant forall k :: 2 <= k < v ==> x % k != 0
    decreases x - v * v
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  return true;
}

method isPalindrome(x: int) returns (palindrome: bool)
  requires x >= 0
{
  var reversed := reverse(x);
  palindrome := (x == reversed);
}

method reverse(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  result := 0;
  var temp := x;
  while temp > 0
    invariant temp >= 0
    invariant result >= 0
    decreases temp
  {
    result := result * 10 + temp % 10;
    temp := temp / 10;
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= -2147483648 && result <= 2147483647
{
  var k := 0;
  var stk := new int[4 * n + 1];
  var stkSize := 1;
  stk[0] := n;
  
  var x := n - 1;
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 1 <= stkSize <= 4 * n
    invariant 0 <= k <= 3
    invariant forall i :: 0 <= i < stkSize ==> stk[i] >= -2147483648 && stk[i] <= 2147483647
    decreases x
  {
    if k == 0 {
      stkSize := stkSize - 1;
      var top := stk[stkSize];
      var product := top * x;
      if product > 2147483647 {
        product := 2147483647;
      } else if product < -2147483648 {
        product := -2147483648;
      }
      stk[stkSize] := product;
      stkSize := stkSize + 1;
    } else if k == 1 {
      stkSize := stkSize - 1;
      var top := stk[stkSize];
      var quotient := top / x;
      stk[stkSize] := quotient;
      stkSize := stkSize + 1;
    } else if k == 2 {
      if stkSize < 4 * n {
        stk[stkSize] := x;
        stkSize := stkSize + 1;
      }
    } else {
      if stkSize < 4 * n {
        stk[stkSize] := -x;
        stkSize := stkSize + 1;
      }
    }
    k := (k + 1) % 4;
    x := x - 1;
  }
  
  result := 0;
  var i := 0;
  while i < stkSize
    invariant 0 <= i <= stkSize
    invariant result >= -2147483648 && result <= 2147483647
    invariant forall j :: 0 <= j < stkSize ==> stk[j] >= -2147483648 && stk[j] <= 2147483647
  {
    var oldResult := result;
    result := result + stk[i];
    if result < -2147483648 {
      result := -2147483648;
    } else if result > 2147483647 {
      result := 2147483647;
    }
    i := i + 1;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 250
  ensures result >= -2147483648 && result <= 2147483647
{
  var o1 := countTriples_1925(o);
  var o2 := nextBeautifulNumber_2048(o1);
  var o3;
  if o2 <= 1000 {
    o3 := sumOfMultiples_2652(o2);
  } else {
    o3 := 1;
  }
  var o4;
  if o3 <= 100000000 {
    o4 := primePalindrome_866(o3);
  } else {
    o4 := 1;
  }
  if o4 <= 10000 {
    result := clumsy_1006(o4);
  } else {
    result := 0;
  }
}
