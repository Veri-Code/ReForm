
method isPrime(x: int) returns (result: bool)
  requires x >= 0
  ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
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
    decreases x - v * v + 1
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  
  // Need to prove that no divisors exist between v and x
  assert forall k :: 2 <= k < v ==> x % k != 0;
  assert v * v > x;
  
  // For any k where v <= k < x, if k divides x, then x/k < v
  // But x/k >= 2 (since k < x and k >= v >= 2), so x/k would be a divisor < v
  // This contradicts our loop invariant
  assert forall k :: v <= k < x ==> x % k != 0 by {
    forall k | v <= k < x
      ensures x % k != 0
    {
      if x % k == 0 {
        var quotient := x / k;
        assert quotient * k == x;
        assert quotient >= 2;
        assert quotient < v;
        assert x % quotient == 0;
        assert false;
      }
    }
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
    decreases temp
  {
    res := res * 10 + temp % 10;
    temp := temp / 10;
  }
  return res;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures 1 <= result
  ensures result >= n
  decreases *
{
  var current := n;
  
  while true
    invariant current >= n
    invariant current >= 1
    decreases *
  {
    var rev := reverse(current);
    if rev == current {
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

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant |stk| >= 1
    invariant 0 <= k <= 3
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
  
  var sum := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
    decreases |stk| - i
  {
    sum := sum + stk[i];
    i := i + 1;
  }
  
  return if sum >= 1 then sum else 1;
}

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 0 <= result < 1000000007
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
    invariant forall idx :: 0 <= idx < j ==> 0 <= f[idx] < mod
    decreases n + 1 - j
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant forall idx :: 0 <= idx < j ==> 0 <= f[idx] < mod
    decreases n + 1 - j
  {
    f[j] := (f[j] + f[j - 2]) % mod;
    j := j + 1;
  }
  
  if n >= 6 {
    j := 6;
    while j <= n
      invariant 6 <= j <= n + 1
      invariant forall idx :: 0 <= idx < j ==> 0 <= f[idx] < mod
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
  
  return ans;
}

method intToString(num: int) returns (result: seq<char>)
  requires num >= 0
  ensures |result| >= 1
  ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
  if num == 0 {
    return ['0'];
  }
  
  var digits := [];
  var temp := num;
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    invariant temp > 0 ==> |digits| >= 0
    invariant temp == 0 ==> |digits| >= 1
    decreases temp
  {
    var digit := temp % 10;
    var digitChar := ('0' as int + digit) as char;
    digits := [digitChar] + digits;
    temp := temp / 10;
  }
  
  assert temp == 0;
  assert |digits| >= 1;
  return digits;
}

method stringToInt(s: seq<char>) returns (result: int)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures result >= 0
{
  var res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res >= 0
    decreases |s| - i
  {
    var digit := (s[i] as int) - ('0' as int);
    res := res * 10 + digit;
    i := i + 1;
  }
  return res;
}

method maximumSwap_670(num: int) returns (result: int)
  requires 0 <= num <= 100000000
  ensures 0 <= result
{
  var s := intToString(num);
  var n := |s|;
  var d := new int[n];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> d[j] == j
    decreases n - i
  {
    d[i] := i;
    i := i + 1;
  }
  
  i := n - 2;
  while i >= 0
    invariant -1 <= i <= n - 2
    invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    decreases i + 1
  {
    if s[i] <= s[d[i + 1]] {
      d[i] := d[i + 1];
    }
    i := i - 1;
  }
  
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < n ==> 0 <= d[j] < n
    invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    decreases n - i
  {
    var j := d[i];
    if s[i] < s[j] {
      var temp := s[i];
      s := s[i := s[j]];
      s := s[j := temp];
      break;
    }
    i := i + 1;
  }
  
  result := stringToInt(s);
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures 0 <= result
{
  var s := intToString(n);
  var i := 1;
  
  while i < |s| && s[i - 1] <= s[i]
    invariant 1 <= i <= |s|
    decreases |s| - i
  {
    i := i + 1;
  }
  
  if i < |s| {
    while i > 0 && s[i - 1] > s[i]
      invariant 0 <= i < |s|
      invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
      decreases i
    {
      var digit := (s[i - 1] as int) - ('0' as int);
      digit := digit - 1;
      if digit >= 0 {
        var newChar := ('0' as int + digit) as char;
        s := s[i - 1 := newChar];
      }
      i := i - 1;
    }
    i := i + 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
      decreases |s| - i
    {
      s := s[i := '9'];
      i := i + 1;
    }
  }
  
  result := stringToInt(s);
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures 0 <= result
  decreases *
{
  var o1 := primePalindrome_866(o);
  var o2 := clumsy_1006(if o1 <= 10000 then o1 else 10000);
  var o3 := numberOfWays_3183(if o2 <= 100000 then o2 else 100000);
  var o4 := maximumSwap_670(if o3 <= 100000000 then o3 else 100000000);
  var o5 := monotoneIncreasingDigits_738(if o4 <= 1000000000 then o4 else 1000000000);
  return o5;
}
