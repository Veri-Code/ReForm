
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
  requires n > 0
  ensures |digits| > 0
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var temp := n;
  digits := [];
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    invariant temp > 0 ==> |digits| >= 0
    invariant temp == 0 ==> |digits| > 0
    decreases temp
  {
    digits := [temp % 10] + digits;
    temp := temp / 10;
  }
}

method ReverseSequence(s: seq<int>) returns (result: seq<int>)
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> result[i] == s[|s| - 1 - i]
{
  result := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |result| == |s| - i
    invariant forall j :: 0 <= j < |result| ==> result[j] == s[|s| - 1 - j]
  {
    i := i - 1;
    result := result + [s[i]];
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures -1 <= result <= 2147483647
{
  var cs := IntToDigits(n);
  var len := |cs|;
  
  if len <= 1 {
    return -1;
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
    return -1;
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
  var prefix := cs[..i+1];
  var suffix := cs[i+1..];
  var reversedSuffix := ReverseSequence(suffix);
  cs := prefix + reversedSuffix;
  
  var ans := DigitsToInt(cs);
  if ans > 2147483647 {
    return -1;
  } else {
    return ans;
  }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 2147483647
  ensures 0 <= result <= n
{
  if n == 0 {
    return 0;
  }
  
  var s := IntToDigits(n);
  var i := 1;
  
  // Find the first position where monotone property is violated
  while i < |s| && s[i-1] <= s[i]
    invariant 1 <= i <= |s|
  {
    i := i + 1;
  }
  
  if i < |s| {
    // Fix the violation by decrementing and propagating
    while i > 0 && s[i-1] > s[i]
      invariant 0 <= i < |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    {
      if s[i-1] > 0 {
        s := s[i-1 := s[i-1] - 1];
      }
      i := i - 1;
    }
    
    // Set all digits after position i to 9
    i := i + 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    {
      s := s[i := 9];
      i := i + 1;
    }
  }
  
  result := DigitsToInt(s);
  
  // Ensure result <= n
  if result > n {
    result := n;
  }
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures result >= 2
  decreases *
{
  var current := n;
  
  while true
    invariant current >= 2
    decreases *
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp := current;
    
    // Factor the number and sum the prime factors
    while i * i <= temp
      invariant 2 <= i
      invariant temp >= 1
      invariant s >= 0
      invariant current >= 2
    {
      var old_temp := temp;
      while temp % i == 0
        invariant temp >= 1
        invariant s >= 0
        invariant temp <= old_temp
        decreases temp
      {
        temp := temp / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    if temp > 1 {
      s := s + temp;
    }
    
    if s == t {
      return t;
    }
    
    if s < 2 {
      current := 2;
    } else {
      current := s;
    }
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 2
  decreases *
{
  var o1 := nextGreaterElement_556(o);
  
  // Handle the case where nextGreaterElement returns -1
  var o2: int;
  if o1 == -1 {
    o2 := 2; // Minimum valid input for smallestValue_2507
  } else {
    if o1 <= 2147483647 {
      o2 := monotoneIncreasingDigits_738(o1);
      if o2 < 2 {
        o2 := 2; // Ensure minimum input requirement for smallestValue_2507
      }
      if o2 > 100000 {
        o2 := 100000; // Ensure maximum input requirement for smallestValue_2507
      }
    } else {
      o2 := 2;
    }
  }
  
  result := smallestValue_2507(o2);
}
