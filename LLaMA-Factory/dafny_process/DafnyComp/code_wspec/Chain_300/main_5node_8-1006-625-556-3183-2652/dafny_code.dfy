
method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 2147483648
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 0 <= k <= 3
    invariant |stk| >= 1
    decreases x
  {
    if k == 0 {
      var top := stk[|stk| - 1];
      stk := stk[..|stk| - 1] + [top * x];
    } else if k == 1 {
      var top := stk[|stk| - 1];
      stk := stk[..|stk| - 1] + [top / x];
    } else if k == 2 {
      stk := stk + [x];
    } else {
      stk := stk + [-x];
    }
    k := (k + 1) % 4;
    x := x - 1;
  }
  
  result := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
    decreases |stk| - i
  {
    result := result + stk[i];
    i := i + 1;
  }
  
  if result <= 0 {
    result := 1;
  }
  if result > 2147483648 {
    result := 2147483648;
  }
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 1 <= result <= 2147483648
{
  if num < 2 {
    result := num;
    return;
  }
  
  var ans := 0;
  var mul := 1;
  var remaining := num;
  var i := 9;
  
  while i > 1
    invariant 1 <= i <= 9
    invariant remaining >= 1
    invariant mul >= 1
    invariant ans >= 0
    decreases i
  {
    while remaining % i == 0
      invariant remaining >= 1
      invariant mul >= 1
      invariant ans >= 0
      decreases remaining
    {
      remaining := remaining / i;
      ans := mul * i + ans;
      mul := mul * 10;
    }
    i := i - 1;
  }
  
  if remaining < 2 && ans <= 2147483647 && ans > 0 {
    result := ans;
  } else {
    result := 1;
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures 1 <= result <= 100000
{
  var digits := [];
  var temp := n;
  
  while temp > 0
    invariant temp >= 0
    decreases temp
  {
    digits := [temp % 10] + digits;
    temp := temp / 10;
  }
  
  if |digits| == 0 {
    result := 1;
    return;
  }
  
  var len := |digits|;
  var i := len - 2;
  
  while i >= 0 && digits[i] >= digits[i + 1]
    invariant -1 <= i < len - 1
    decreases i + 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    result := 1;
    return;
  }
  
  var j := len - 1;
  while digits[i] >= digits[j]
    invariant i < j < len
    decreases j
  {
    j := j - 1;
  }
  
  var temp_digit := digits[i];
  digits := digits[i := digits[j]];
  digits := digits[j := temp_digit];
  
  var left := i + 1;
  var right := len - 1;
  while left < right
    invariant i + 1 <= left <= right + 1 <= len
    invariant 0 <= left < |digits|
    invariant 0 <= right < |digits|
    decreases right - left
  {
    temp_digit := digits[left];
    digits := digits[left := digits[right]];
    digits := digits[right := temp_digit];
    left := left + 1;
    right := right - 1;
  }
  
  result := 0;
  var k := 0;
  while k < |digits|
    invariant 0 <= k <= |digits|
    decreases |digits| - k
  {
    if result <= 214748364 {
      result := result * 10 + digits[k];
    }
    k := k + 1;
  }
  
  if result > 100000 {
    result := 100000;
  }
  if result < 1 {
    result := 1;
  }
}

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 1000
{
  var mod := 1000000007;
  var f := new int[n + 1];
  var i := 0;
  
  while i <= n
    invariant 0 <= i <= n + 1
    decreases n + 1 - i
  {
    f[i] := 0;
    i := i + 1;
  }
  f[0] := 1;
  
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant f[0] == 1
    decreases n + 1 - j
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    decreases n + 1 - j
  {
    f[j] := (f[j] + f[j - 2]) % mod;
    j := j + 1;
  }
  
  if n >= 6 {
    j := 6;
    while j <= n
      invariant 6 <= j <= n + 1
      decreases n + 1 - j
    {
      f[j] := (f[j] + f[j - 6]) % mod;
      j := j + 1;
    }
  }
  
  var ans := f[n];
  if n >= 4 {
    ans := (ans + f[n - 4]) % mod;
  }
  if n >= 8 {
    ans := (ans + f[n - 8]) % mod;
  }
  
  result := (ans % 1000);
  if result == 0 {
    result := 1;
  }
}

method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures result >= 0
{
  result := 0;
  var x := 1;
  
  while x <= n
    invariant 1 <= x <= n + 1
    invariant result >= 0
    decreases n + 1 - x
  {
    if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
      result := result + x;
    }
    x := x + 1;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures result >= 0
{
  var o1 := clumsy_1006(o);
  var o2 := smallestFactorization_625(o1);
  var o3 := nextGreaterElement_556(o2);
  var o4 := numberOfWays_3183(o3);
  var o5 := sumOfMultiples_2652(o4);
  result := o5;
}
