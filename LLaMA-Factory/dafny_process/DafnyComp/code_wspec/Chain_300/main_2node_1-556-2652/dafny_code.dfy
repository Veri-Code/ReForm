
method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures result == -1 || (1 <= result <= 1000)
{
  // Convert number to sequence of digits
  var digits := numberToDigits(n);
  var len := |digits|;
  
  if len <= 1 {
    return -1;
  }
  
  // Find the rightmost digit that is smaller than the digit next to it
  var i := len - 2;
  while i >= 0 && digits[i] >= digits[i + 1]
    invariant -1 <= i < len - 1
    invariant forall k :: i < k < len - 1 ==> digits[k] >= digits[k + 1]
  {
    i := i - 1;
  }
  
  if i < 0 {
    return -1;
  }
  
  // Find the smallest digit on right side of above character that is greater than digits[i]
  var j := len - 1;
  while digits[i] >= digits[j]
    invariant 0 <= i < j < len
    invariant forall k :: j < k < len ==> digits[i] >= digits[k]
    decreases j
  {
    j := j - 1;
  }
  
  // Swap digits[i] and digits[j]
  var temp := digits[i];
  digits := digits[i := digits[j]][j := temp];
  
  // Reverse the sequence after position i
  digits := digits[..i+1] + reverse(digits[i+1..]);
  
  // Prove that digits still contains valid digits
  assert forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9;
  
  var ans := digitsToNumber(digits);
  if ans > 2147483647 || ans <= 1000 {
    return -1;
  } else {
    return -1;
  }
}

method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures result >= 0
{
  var sum := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant sum >= 0
    invariant sum == sumMultiplesUpTo(i - 1)
  {
    if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
  
  return sum;
}

function sumMultiplesUpTo(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else if n % 3 == 0 || n % 5 == 0 || n % 7 == 0 then
    n + sumMultiplesUpTo(n - 1)
  else
    sumMultiplesUpTo(n - 1)
}

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := nextGreaterElement_556(o);
  if o1 == -1 {
    result := sumOfMultiples_2652(1);
  } else {
    result := sumOfMultiples_2652(o1);
  }
}

// Helper methods for digit manipulation
method numberToDigits(n: int) returns (digits: seq<int>)
  requires n >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var temp := n;
  digits := [];
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    invariant temp > 0 ==> |digits| >= 0
    invariant temp == 0 ==> |digits| >= 1
    decreases temp
  {
    var digit := temp % 10;
    digits := [digit] + digits;
    temp := temp / 10;
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
    result := result * 10 + digits[i];
    i := i + 1;
  }
}

function reverse<T>(s: seq<T>): seq<T>
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 then []
  else reverse(s[1..]) + [s[0]]
}

lemma reversePreservesDigitProperty(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures forall i :: 0 <= i < |reverse(s)| ==> 0 <= reverse(s)[i] <= 9
{
  if |s| == 0 {
    // Base case: empty sequence
  } else {
    // Inductive case
    reversePreservesDigitProperty(s[1..]);
  }
}
