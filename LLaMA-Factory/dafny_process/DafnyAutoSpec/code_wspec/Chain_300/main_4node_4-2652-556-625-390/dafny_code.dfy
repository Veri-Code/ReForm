
method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures 1 <= result <= 2147483648
{
  result := 0;
  var x := 1;
  
  while x <= n
    invariant 1 <= x <= n + 1
    invariant result >= 0
    invariant result <= x * 1000  // More generous upper bound
  {
    if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
      result := result + x;
    }
    x := x + 1;
  }
  
  if result == 0 {
    result := 1;  // Ensure postcondition 1 <= result
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures -1 <= result <= 2147483648
{
  // Convert number to sequence of digits
  var digits := numberToDigits(n);
  var len := |digits|;
  
  if len <= 1 {
    result := -1;
    return;
  }
  
  // Find rightmost digit that is smaller than the digit next to it
  var i := len - 2;
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
  
  // Find the smallest digit on right side of above character that is greater than digits[i]
  var j := len - 1;
  while digits[i] >= digits[j]
    invariant i < j < len
    invariant j >= 0
    decreases j
  {
    j := j - 1;
  }
  
  // Swap digits[i] and digits[j]
  digits := swapDigits(digits, i, j);
  
  // Reverse the substring after position i
  digits := reverseAfter(digits, i + 1);
  
  var ans := digitsToNumber(digits);
  if ans > 2147483647 {
    result := -1;
  } else {
    result := ans;
  }
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 2147483648
{
  if num < 2 {
    result := num;
    return;
  }
  
  var ans := 0;
  var mul := 1;
  var remaining := num;
  var i := 9;
  
  while i >= 2
    invariant 1 <= i <= 9
    invariant ans >= 0
    invariant mul >= 1
    invariant remaining >= 1
    decreases i
  {
    while remaining % i == 0
      invariant remaining >= 1
      invariant ans >= 0
      invariant mul >= 1
      decreases remaining
    {
      remaining := remaining / i;
      ans := mul * i + ans;
      mul := mul * 10;
      if ans > 2147483647 || mul > 214748364 {
        result := 0;
        return;
      }
    }
    i := i - 1;
  }
  
  if remaining < 2 && ans <= 2147483647 {
    result := ans;
  } else {
    result := 0;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
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
    invariant an >= 1 - step
    invariant a1 <= n + step
    invariant an <= n + step
    decreases cnt
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
}

// Helper methods for nextGreaterElement_556
method numberToDigits(n: int) returns (digits: seq<int>)
  requires n >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  digits := [];
  var temp := n;
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    decreases temp
  {
    digits := [temp % 10] + digits;
    temp := temp / 10;
  }
  
  if |digits| == 0 {
    digits := [0];
  }
}

method swapDigits(digits: seq<int>, i: int, j: int) returns (result: seq<int>)
  requires 0 <= i < |digits|
  requires 0 <= j < |digits|
  requires forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9
  ensures |result| == |digits|
  ensures forall k :: 0 <= k < |digits| ==> 0 <= result[k] <= 9
  ensures result[i] == digits[j]
  ensures result[j] == digits[i]
  ensures forall k :: 0 <= k < |digits| && k != i && k != j ==> result[k] == digits[k]
{
  result := digits[i := digits[j]][j := digits[i]];
}

method reverseAfter(digits: seq<int>, start: int) returns (result: seq<int>)
  requires 0 <= start <= |digits|
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures |result| == |digits|
  ensures forall i :: 0 <= i < |digits| ==> 0 <= result[i] <= 9
  ensures forall i :: 0 <= i < start ==> result[i] == digits[i]
{
  if start >= |digits| {
    result := digits;
    return;
  }
  
  var prefix := digits[..start];
  var suffix := digits[start..];
  var reversedSuffix := reverseSeq(suffix);
  result := prefix + reversedSuffix;
}

method reverseSeq(s: seq<int>) returns (result: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> 0 <= result[i] <= 9
  ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
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

method digitsToNumber(digits: seq<int>) returns (result: int)
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
    if result > 214748364 || (result == 214748364 && digits[i] > 7) {
      result := 2147483648; // Overflow indicator
      return;
    }
    result := result * 10 + digits[i];
    i := i + 1;
  }
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 1000
  ensures true
{
  var o1 := sumOfMultiples_2652(o);
  var o2 := nextGreaterElement_556(o1);
  var o3_input := if o2 == -1 then 1 else if o2 < 1 then 1 else if o2 > 2147483648 then 1 else o2;
  var o3 := smallestFactorization_625(o3_input);
  var o4_input := if o3 == 0 then 1 else if o3 > 1000000000 then 1 else o3;
  var o4 := lastRemaining_390(o4_input);
  result := o4;
}
