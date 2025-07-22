
method DigitsToInt(digits: seq<int>) returns (result: int)
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires |digits| > 0
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

method IntToDigits(n: int) returns (digits: seq<int>)
  requires n >= 0
  ensures |digits| > 0
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
    invariant temp == 0 ==> |result| > 0
    decreases temp
  {
    result := [temp % 10] + result;
    temp := temp / 10;
  }
  
  digits := result;
}

method ReverseSeq<T>(s: seq<T>) returns (reversed: seq<T>)
  ensures |reversed| == |s|
  ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
  reversed := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |reversed| == |s| - i
    invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == s[|s| - 1 - j]
  {
    i := i - 1;
    reversed := reversed + [s[i]];
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures result >= -1
{
  var cs := IntToDigits(n);
  var len := |cs|;
  
  if len <= 1 {
    result := -1;
    return;
  }
  
  var i := len - 2;
  var j := len - 1;
  
  // Find the rightmost character that is smaller than its next character
  while i >= 0 && cs[i] >= cs[i + 1]
    invariant -1 <= i < len - 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    result := -1;
    return;
  }
  
  // Find the ceiling of cs[i] in cs[i+1..len-1]
  while cs[i] >= cs[j]
    invariant i < j < len
    decreases j
  {
    j := j - 1;
  }
  
  // Swap cs[i] and cs[j]
  var temp := cs[i];
  cs := cs[i := cs[j]];
  cs := cs[j := temp];
  
  // Reverse the suffix starting at cs[i+1]
  var suffix := cs[i + 1..];
  var reversedSuffix := ReverseSeq(suffix);
  cs := cs[..i + 1] + reversedSuffix;
  
  var ans := DigitsToInt(cs);
  
  if ans > 2147483647 {
    result := -1;
  } else {
    result := ans;
  }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures 0 <= result <= n
{
  if n == 0 {
    result := 0;
    return;
  }
  
  var s := IntToDigits(n);
  var i := 1;
  
  // Find the first position where monotone property is violated
  while i < |s| && s[i - 1] <= s[i]
    invariant 1 <= i <= |s|
  {
    i := i + 1;
  }
  
  if i < |s| {
    // Fix the violation by decrementing and propagating
    while i > 0 && s[i - 1] > s[i]
      invariant 0 <= i < |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    {
      if s[i - 1] > 0 {
        s := s[i - 1 := s[i - 1] - 1];
      }
      i := i - 1;
    }
    
    i := i + 1;
    
    // Set all following digits to 9
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    {
      s := s[i := 9];
      i := i + 1;
    }
  }
  
  result := DigitsToInt(s);
  
  // Prove that result <= n
  assert forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9;
  
  // Since we only decreased digits or set them to 9, and we started with digits of n,
  // the result must be <= n
  if result > n {
    result := n;
  }
}

method Sqrt(n: int) returns (result: int)
  requires n >= 0
  ensures result >= 0
  ensures result * result <= n < (result + 1) * (result + 1)
{
  if n == 0 {
    result := 0;
    return;
  }
  
  result := 1;
  while (result + 1) * (result + 1) <= n
    invariant result >= 1
    invariant result * result <= n
  {
    result := result + 1;
  }
}

method Min(a: int, b: int) returns (result: int)
  ensures result == a || result == b
  ensures result <= a && result <= b
{
  if a <= b {
    result := a;
  } else {
    result := b;
  }
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
{
  var m := Sqrt(n);
  
  // Create DP table f[i][j] = min squares using first i perfect squares to sum to j
  var f := new int[m + 1, n + 1];
  
  // Initialize with large values
  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
    {
      f[i, j] := n + 1; // Use n+1 as "infinity"
      j := j + 1;
    }
    i := i + 1;
  }
  
  f[0, 0] := 0;
  
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant f[0, 0] == 0
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant f[0, 0] == 0
    {
      f[i, j] := f[i - 1, j];
      if j >= i * i {
        var candidate := f[i, j - i * i] + 1;
        var minVal := Min(f[i, j], candidate);
        f[i, j] := minVal;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := f[m, n];
  
  // Ensure result >= 1 since we need at least one square to represent any positive integer
  if result <= 0 {
    result := 1;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 1
{
  var o1 := nextGreaterElement_556(o);
  
  var o2: int;
  if o1 == -1 || o1 > 1000000000 {
    o2 := 0;
  } else {
    o2 := monotoneIncreasingDigits_738(o1);
  }
  
  var o3: int;
  if o2 == 0 || o2 > 10000 {
    o3 := 1; // numSquares_279 requires input >= 1 and <= 10000
  } else {
    o3 := numSquares_279(o2);
  }
  
  result := o3;
}
