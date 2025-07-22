
function digitToInt(c: char): int
  requires '0' <= c <= '9'
  ensures 0 <= digitToInt(c) <= 9
  ensures digitToInt(c) == (c as int) - ('0' as int)
{
  (c as int) - ('0' as int)
}

function intToChar(i: int): char
  requires 0 <= i <= 9
  ensures '0' <= intToChar(i) <= '9'
  ensures intToChar(i) == (('0' as int) + i) as char
{
  (('0' as int) + i) as char
}

method stringToInt(s: seq<char>) returns (result: int)
  requires |s| > 0
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
  return res;
}

method intToString(n: int) returns (result: seq<char>)
  requires n >= 0
  ensures |result| > 0
  ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
  if n == 0 {
    return ['0'];
  }
  
  var digits: seq<char> := [];
  var num := n;
  
  while num > 0
    invariant num >= 0
    invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    invariant num > 0 ==> |digits| >= 0
    invariant num == 0 ==> |digits| > 0
  {
    var digit := num % 10;
    var digitChar := intToChar(digit);
    digits := [digitChar] + digits;
    num := num / 10;
  }
  
  return digits;
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 1000000000
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
    invariant ans <= 1000000000
    invariant mul <= 1000000000
    decreases i
  {
    while n % i == 0
      invariant n >= 1
      invariant mul >= 1
      invariant ans >= 0
      invariant ans <= 1000000000
      invariant mul <= 1000000000
      decreases n
    {
      n := n / i;
      if mul > 1000000000 / 10 {
        return 0;
      }
      var newAns := mul * i + ans;
      if newAns > 1000000000 {
        return 0;
      }
      ans := newAns;
      mul := mul * 10;
    }
    i := i - 1;
  }
  
  if n < 2 && ans <= 2147483647 {
    return ans;
  } else {
    return 0;
  }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures 1 <= result <= 1000000000
{
  if n == 0 {
    return 1;
  }
  
  var s := intToString(n);
  var i := 1;
  
  while i < |s| && digitToInt(s[i-1]) <= digitToInt(s[i])
    invariant 1 <= i <= |s|
  {
    i := i + 1;
  }
  
  if i < |s| {
    while i > 0 && i < |s| && digitToInt(s[i-1]) > digitToInt(s[i])
      invariant 0 <= i < |s|
      invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    {
      var prevDigit := digitToInt(s[i-1]);
      if prevDigit > 0 {
        s := s[i-1 := intToChar(prevDigit - 1)];
      }
      i := i - 1;
    }
    
    i := i + 1;
    while i < |s|
      invariant i <= |s|
      invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    {
      s := s[i := '9'];
      i := i + 1;
    }
  }
  
  var res := stringToInt(s);
  if res >= 1 && res <= 1000000000 {
    return res;
  } else {
    return 1;
  }
}

method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures result >= 0
{
  var ans := 0;
  var cnt := 0;
  var num := n;
  
  while num > 0
    invariant num >= 0
    invariant ans >= 0
    invariant cnt >= 0
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
  
  return ans;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := smallestFactorization_625(o);
  if o1 == 0 {
    return 0;
  }
  
  var o2 := monotoneIncreasingDigits_738(o1);
  var o3 := minOperations_2571(o2);
  return o3;
}
