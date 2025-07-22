
method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 0 <= result <= 10000000000
  decreases *
{
  var a := 0;
  var b := 0;
  var k := 0;
  var t := n;
  
  while t > 0
    invariant a >= 0 && b >= 0 && k >= 0
    invariant a + b == k
    decreases t
  {
    if (t % 10) % 2 == 1 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    t := t / 10;
    k := k + 1;
  }
  
  if k % 2 == 1 {
    var x := pow10(k);
    var y := if k / 2 == 0 then 0 else repunit(k / 2);
    result := x + y;
    assert result >= 0;
    if result > 10000000000 {
      result := 10000000000;
    }
  } else if a == b {
    result := n;
  } else {
    if n < 1000000000 {
      result := closestFair_2417(n + 1);
    } else {
      result := 10000000000;
    }
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 10000000000
  ensures 1 <= result <= 2147483648
  decreases *
{
  var x := n + 1;
  
  while x <= 2147483648
    invariant x >= n + 1
    decreases 2147483648 - x + 1
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
      var v := y % 10;
      cnt[v] := cnt[v] + 1;
      y := y / 10;
    }
    
    var isBeautiful := true;
    i := 0;
    while i < 10 && isBeautiful
      invariant 0 <= i <= 10
    {
      if cnt[i] != 0 && i != cnt[i] {
        isBeautiful := false;
      }
      i := i + 1;
    }
    
    if isBeautiful {
      result := x;
      return;
    }
    x := x + 1;
  }
  
  result := 2147483648;
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures -1 <= result <= 2147483648
{
  var digits := intToDigits(n);
  var len := |digits|;
  
  if len == 0 {
    result := -1;
    return;
  }
  
  var i := len - 2;
  var j := len - 1;
  
  while i >= 0 && digits[i] >= digits[i + 1]
    invariant -1 <= i < len - 1
    decreases i + 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    result := -1;
    return;
  }
  
  while digits[i] >= digits[j]
    invariant 0 <= i < j < len
    decreases j - i
  {
    j := j - 1;
  }
  
  digits := swap(digits, i, j);
  digits := reverseFrom(digits, i + 1);
  
  var ans := digitsToInt(digits);
  if ans > 2147483647 {
    result := -1;
  } else {
    result := ans;
  }
}

method primePalindrome_866(n: int) returns (result: int)
  requires -1 <= n <= 2147483648
  ensures 1 <= result <= 200000000
  decreases *
{
  var current := if n <= 0 then 1 else n;
  
  while current <= 200000000
    invariant current >= 1
    decreases 200000000 - current + 1
  {
    if isPalindrome(current) && isPrime(current) {
      result := current;
      return;
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
  }
  
  result := 200000000;
}

method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 200000000
  ensures result >= 0
{
  var ans := 0;
  var cnt := 0;
  var num := n;
  
  while num > 0
    invariant num >= 0 && ans >= 0 && cnt >= 0
    decreases num
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
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 1000000
  ensures result >= 0
  decreases *
{
  var o1 := closestFair_2417(o);
  var o2 := nextBeautifulNumber_2048(o1);
  var o3 := nextGreaterElement_556(o2);
  var o4 := primePalindrome_866(o3);
  var o5 := minOperations_2571(o4);
  result := o5;
}

// Helper methods

function pow10(k: int): int
  requires k >= 0
  ensures pow10(k) > 0
  decreases k
{
  if k == 0 then 1 else 10 * pow10(k - 1)
}

function repunit(k: int): int
  requires k >= 0
  ensures repunit(k) >= 0
  decreases k
{
  if k == 0 then 0 else 10 * repunit(k - 1) + 1
}

method intToDigits(n: int) returns (digits: seq<int>)
  requires n >= 0
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  if n == 0 {
    digits := [0];
    return;
  }
  
  var temp := n;
  var result: seq<int> := [];
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
    invariant temp > 0 ==> |result| >= 0
    invariant temp == 0 ==> |result| >= 1
    decreases temp
  {
    result := [temp % 10] + result;
    temp := temp / 10;
  }
  
  digits := result;
}

method digitsToInt(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  result := 0;
  var i := 0;
  
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant result >= 0
  {
    result := result * 10 + digits[i];
    i := i + 1;
  }
}

function swap(s: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures |swap(s, i, j)| == |s|
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> swap(s, i, j)[k] == s[k]
  ensures swap(s, i, j)[i] == s[j]
  ensures swap(s, i, j)[j] == s[i]
  ensures (forall k :: 0 <= k < |s| ==> 0 <= s[k] <= 9) ==> (forall k :: 0 <= k < |s| ==> 0 <= swap(s, i, j)[k] <= 9)
{
  s[i := s[j]][j := s[i]]
}

function reverseFrom(s: seq<int>, start: int): seq<int>
  requires 0 <= start <= |s|
  ensures |reverseFrom(s, start)| == |s|
  ensures (forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9) ==> (forall i :: 0 <= i < |s| ==> 0 <= reverseFrom(s, start)[i] <= 9)
{
  s[..start] + reverse(s[start..])
}

function reverse(s: seq<int>): seq<int>
  ensures |reverse(s)| == |s|
  ensures (forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9) ==> (forall i :: 0 <= i < |s| ==> 0 <= reverse(s)[i] <= 9)
  decreases |s|
{
  if |s| <= 1 then s else reverse(s[1..]) + [s[0]]
}

predicate isPalindrome(n: int)
  requires n >= 0
{
  var digits := intToDigitsFunc(n);
  digits == reverse(digits)
}

function intToDigitsFunc(n: int): seq<int>
  requires n >= 0
  ensures |intToDigitsFunc(n)| >= 1
  ensures forall i :: 0 <= i < |intToDigitsFunc(n)| ==> 0 <= intToDigitsFunc(n)[i] <= 9
  decreases n
{
  if n < 10 then [n] else intToDigitsFunc(n / 10) + [n % 10]
}

predicate isPrime(n: int)
  requires n >= 0
{
  n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
