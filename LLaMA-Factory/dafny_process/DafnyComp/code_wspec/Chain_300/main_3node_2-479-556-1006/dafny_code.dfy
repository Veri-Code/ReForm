
method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 2147483648
{
  var mx := power10(n) - 1;
  var a := mx;
  
  while a > mx / 10
    invariant mx / 10 <= a <= mx
    invariant mx == power10(n) - 1
    decreases a
  {
    // Create palindrome by mirroring a
    var b := a;
    var x := a;
    while b > 0
      invariant b >= 0
      invariant x >= a
      decreases b
    {
      x := x * 10 + b % 10;
      b := b / 10;
    }
    
    // Check if x can be expressed as product of two n-digit numbers
    var t := mx;
    while t * t >= x && t > 0
      invariant t >= 0
      invariant t <= mx
      decreases t
    {
      if x % t == 0 {
        var quotient := x / t;
        if quotient <= mx && quotient > mx / 10 {
          var res := x % 1337;
          if res == 0 {
            return 1337;
          } else {
            return res;
          }
        }
      }
      t := t - 1;
    }
    a := a - 1;
  }
  return 9;
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures -1 <= result <= 2147483647
{
  var digits := intToDigits(n);
  var len := |digits|;
  
  if len <= 1 {
    return -1;
  }
  
  var i := len - 2;
  
  // Find rightmost character that is smaller than its next character
  while i >= 0 && digits[i] >= digits[i + 1]
    invariant -1 <= i < len - 1
    decreases i + 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    return -1;
  }
  
  // Find the smallest character on right side of above character that is greater than above character
  var j := len - 1;
  while j > i && digits[i] >= digits[j]
    invariant i < j < len
    decreases j
  {
    j := j - 1;
  }
  
  // Swap the found characters
  digits := swapDigits(digits, i, j);
  
  // Reverse the substring after position i
  digits := reverseSubarray(digits, i + 1);
  
  var ans := digitsToInt(digits);
  if ans > 2147483647 {
    return -1;
  } else {
    return ans;
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x < n
    invariant |stk| >= 1
    invariant 0 <= k < 4
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
  
  result := sumArray(stk);
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 8
  ensures true
{
  var o1 := largestPalindrome_479(o);
  var o2 := nextGreaterElement_556(o1);
  if o2 >= 1 && o2 <= 10000 {
    result := clumsy_1006(o2);
  } else {
    result := 0;
  }
}

// Helper functions
function power10(n: int): int
  requires 0 <= n <= 8
  ensures power10(n) > 0
{
  if n == 0 then 1
  else if n == 1 then 10
  else if n == 2 then 100
  else if n == 3 then 1000
  else if n == 4 then 10000
  else if n == 5 then 100000
  else if n == 6 then 1000000
  else if n == 7 then 10000000
  else 100000000
}

method intToDigits(n: int) returns (digits: seq<int>)
  requires n >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  digits := [];
  var temp := n;
  while temp > 0
    invariant temp >= 0
    invariant |digits| >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    invariant temp == 0 ==> |digits| >= 1
    decreases temp
  {
    digits := [temp % 10] + digits;
    temp := temp / 10;
  }
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

method swapDigits(digits: seq<int>, i: int, j: int) returns (result: seq<int>)
  requires 0 <= i < |digits|
  requires 0 <= j < |digits|
  requires i != j
  requires forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
  ensures |result| == |digits|
  ensures result[i] == digits[j]
  ensures result[j] == digits[i]
  ensures forall k :: 0 <= k < |digits| && k != i && k != j ==> result[k] == digits[k]
  ensures forall k :: 0 <= k < |result| ==> 0 <= result[k] <= 9
{
  if i < j {
    result := digits[..i] + [digits[j]] + digits[i+1..j] + [digits[i]] + digits[j+1..];
  } else {
    result := digits[..j] + [digits[i]] + digits[j+1..i] + [digits[j]] + digits[i+1..];
  }
}

method reverseSubarray(digits: seq<int>, start: int) returns (result: seq<int>)
  requires 0 <= start <= |digits|
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures |result| == |digits|
  ensures result[..start] == digits[..start]
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
{
  if start >= |digits| {
    return digits;
  }
  
  var prefix := digits[..start];
  var suffix := digits[start..];
  var reversedSuffix := reverseSeq(suffix);
  result := prefix + reversedSuffix;
}

method reverseSeq(s: seq<int>) returns (result: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
{
  result := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |result| == |s| - i
    invariant forall j :: 0 <= j < |result| ==> result[j] == s[|s| - 1 - j]
    invariant forall j :: 0 <= j < |result| ==> 0 <= result[j] <= 9
    decreases i
  {
    i := i - 1;
    result := result + [s[i]];
  }
}

method sumArray(arr: seq<int>) returns (sum: int)
{
  sum := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
  {
    sum := sum + arr[i];
    i := i + 1;
  }
}
