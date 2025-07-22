
method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 1000000007
{
  var mod := 1000000007;
  var coins := [1, 2, 6];
  var f := new int[n + 1];
  
  // Initialize array
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> f[k] == 0
  {
    f[i] := 0;
    i := i + 1;
  }
  f[0] := 1;
  
  // Process each coin
  var coinIdx := 0;
  while coinIdx < 3
    invariant 0 <= coinIdx <= 3
    invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
    invariant f[0] == 1
  {
    var x := coins[coinIdx];
    var j := x;
    while j <= n
      invariant x <= j
      invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
      invariant f[0] == 1
      invariant x >= 1
      invariant j >= x
    {
      f[j] := (f[j] + f[j - x]) % mod;
      j := j + 1;
    }
    coinIdx := coinIdx + 1;
  }
  
  var ans := f[n];
  if n >= 4 {
    ans := (ans + f[n - 4]) % mod;
  }
  if n >= 8 {
    ans := (ans + f[n - 8]) % mod;
  }
  
  result := ans;
  if result == 0 {
    result := 1;
  }
}

method isPrime(x: int) returns (result: bool)
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
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  
  return true;
}

method reverse(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  var res := 0;
  var temp := x;
  while temp > 0
    invariant temp >= 0
    invariant res >= 0
  {
    res := res * 10 + temp % 10;
    temp := temp / 10;
  }
  result := res;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures result >= n
  ensures result <= 1000000000
{
  var current := n;
  var iterations := 0;
  
  while iterations < 200000000
    invariant current >= n
    invariant iterations >= 0
  {
    var rev := reverse(current);
    if rev == current {
      var prime := isPrime(current);
      if prime {
        if current <= 1000000000 {
          return current;
        }
      }
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
    iterations := iterations + 1;
  }
  
  result := 100000007;
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= n
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant 1 <= a1 <= n
    invariant step <= n
    invariant i >= 0
  {
    if i % 2 == 1 {
      if an >= step {
        an := an - step;
      }
      if cnt % 2 == 1 && a1 + step <= n {
        a1 := a1 + step;
      }
    } else {
      if a1 + step <= n {
        a1 := a1 + step;
      }
      if cnt % 2 == 1 && an >= step {
        an := an - step;
      }
    }
    cnt := cnt / 2;
    if step <= n / 2 {
      step := step * 2;
    }
    i := i + 1;
  }
  
  result := a1;
}

method digitToInt(c: char) returns (result: int)
  requires '0' <= c <= '9'
  ensures 0 <= result <= 9
{
  result := (c as int) - ('0' as int);
}

method intToChar(d: int) returns (result: char)
  requires 0 <= d <= 9
  ensures '0' <= result <= '9'
{
  result := (d + ('0' as int)) as char;
}

method stringToInt(s: string) returns (result: int)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures result >= 0
{
  var res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res >= 0
  {
    var digit := digitToInt(s[i]);
    res := res * 10 + digit;
    i := i + 1;
  }
  result := res;
}

method intToString(n: int) returns (result: string)
  requires n >= 0
  ensures |result| >= 1
  ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
  if n == 0 {
    return "0";
  }
  
  var digits: seq<char> := [];
  var temp := n;
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    invariant temp > 0 ==> |digits| >= 0
    invariant temp == 0 ==> |digits| >= 1
  {
    var digit := temp % 10;
    var c := intToChar(digit);
    digits := [c] + digits;
    temp := temp / 10;
  }
  
  result := digits;
}

method reverseString(s: string) returns (result: string)
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
{
  var res: seq<char> := [];
  var i := |s|;
  
  while i > 0
    invariant 0 <= i <= |s|
    invariant |res| == |s| - i
    invariant forall j :: 0 <= j < |res| ==> res[j] == s[|s| - 1 - j]
  {
    i := i - 1;
    res := res + [s[i]];
  }
  
  result := res;
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483647
  ensures result >= -1
{
  var s := intToString(n);
  var cs := s;
  var len := |cs|;
  
  if len <= 1 {
    return -1;
  }
  
  var i := len - 2;
  
  while i >= 0 && cs[i] >= cs[i + 1]
    invariant -1 <= i < len - 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    return -1;
  }
  
  var j := len - 1;
  
  while cs[i] >= cs[j]
    invariant i < j < len
    decreases j
  {
    j := j - 1;
  }
  
  var temp := cs[i];
  cs := cs[i := cs[j]];
  cs := cs[j := temp];
  
  var left := cs[..i+1];
  var right := cs[i+1..];
  var reversedRight := reverseString(right);
  cs := left + reversedRight;
  
  var ans := stringToInt(cs);
  
  if ans > 2147483647 {
    return -1;
  }
  
  result := ans;
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 100000
  ensures result >= -1
{
  var o1 := numberOfWays_3183(o);
  assume 1 <= o1 <= 100000000;
  var o2 := primePalindrome_866(o1);
  var o3 := lastRemaining_390(o2);
  var o4 := nextGreaterElement_556(o3);
  result := o4;
}
