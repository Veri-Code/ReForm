
method DigitsToInt(digits: seq<int>) returns (result: int)
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires |digits| > 0
  ensures result >= 0
{
  result := 0;
  var multiplier := 1;
  var i := |digits| - 1;
  
  while i >= 0
    invariant -1 <= i < |digits|
    invariant result >= 0
    invariant multiplier > 0
  {
    result := result + digits[i] * multiplier;
    multiplier := multiplier * 10;
    i := i - 1;
  }
}

method IntToDigits(n: int) returns (digits: seq<int>)
  requires n > 0
  ensures |digits| > 0
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  digits := [];
  var temp := n;
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    invariant temp > 0 ==> |digits| >= 0
    invariant temp == 0 ==> |digits| > 0
  {
    digits := [temp % 10] + digits;
    temp := temp / 10;
  }
}

method ReverseSequence(s: seq<int>) returns (reversed: seq<int>)
  ensures |reversed| == |s|
  ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
  reversed := [];
  var i := |s| - 1;
  
  while i >= 0
    invariant -1 <= i < |s|
    invariant |reversed| == |s| - 1 - i
    invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == s[|s| - 1 - j]
  {
    reversed := reversed + [s[i]];
    i := i - 1;
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures result == -1 || (1 <= result <= 2147483648)
{
  var digits := IntToDigits(n);
  var len := |digits|;
  
  if len <= 1 {
    return -1;
  }
  
  var i := len - 2;
  
  // Find the rightmost digit that is smaller than the digit next to it
  while i >= 0 && digits[i] >= digits[i + 1]
    invariant -1 <= i < len - 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    return -1;
  }
  
  var j := len - 1;
  
  // Find the smallest digit on right side of above character that is greater than digits[i]
  while digits[i] >= digits[j]
    invariant i < j < len
    decreases j
  {
    j := j - 1;
  }
  
  // Swap the found characters
  var temp := digits[i];
  digits := digits[i := digits[j]];
  digits := digits[j := temp];
  
  // Reverse the sequence after position i
  var suffix := digits[i + 1..];
  var reversedSuffix := ReverseSequence(suffix);
  digits := digits[..i + 1] + reversedSuffix;
  
  var ans := DigitsToInt(digits);
  
  if ans > 2147483647 {
    return -1;
  } else {
    if ans >= 1 {
      return ans;
    } else {
      return -1;
    }
  }
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures result >= 0
{
  if num < 2 {
    return num;
  }
  
  var ans := 0;
  var mul := 1;
  var remaining := num;
  var i := 9;
  
  while i >= 2
    invariant 1 <= i <= 9
    invariant remaining >= 1
    invariant ans >= 0
    invariant mul >= 1
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
    }
    i := i - 1;
  }
  
  if remaining < 2 && ans <= 2147483647 {
    return ans;
  } else {
    return 0;
  }
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures result >= 0
{
  if n == 0 {
    return 0;
  }
  
  var vis := new bool[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  result := dfs(1, n, vis);
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires vis.Length == n + 1
  modifies vis
  ensures count >= 0
  ensures vis.Length == n + 1
  decreases n + 1 - pos
{
  if pos == n + 1 {
    return 1;
  }
  
  count := 0;
  var j := 1;
  
  while j <= n
    invariant 1 <= j <= n + 1
    invariant count >= 0
    invariant vis.Length == n + 1
  {
    if !vis[j] && (j % pos == 0 || pos % j == 0) {
      vis[j] := true;
      var subCount := dfs(pos + 1, n, vis);
      count := count + subCount;
      vis[j] := false;
    }
    j := j + 1;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := nextGreaterElement_556(o);
  if o1 == -1 {
    result := 0;
    return;
  }
  
  var o2 := smallestFactorization_625(o1);
  if o2 == 0 || o2 > 15 {
    result := 0;
    return;
  }
  
  result := countArrangement_526(o2);
}
