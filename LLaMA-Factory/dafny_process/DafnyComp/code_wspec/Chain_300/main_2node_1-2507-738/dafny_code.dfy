
method smallestValue_2507(n0: int) returns (result: int)
  requires 2 <= n0 <= 100000
  ensures result >= 2
  ensures result <= 1000000000
{
  var n := n0;
  var iterations := 0;
  
  while iterations < 1000
    invariant n >= 1
    invariant iterations >= 0
    decreases 1000 - iterations
  {
    var t := n;
    var s := 0;
    var i := 2;
    var original_n := n;
    
    // Factor n and sum the prime factors
    while i * i <= n
      invariant i >= 2
      invariant s >= 0
      invariant n >= 1
    {
      while n % i == 0
        invariant i >= 2
        invariant n >= 1
        invariant s >= 0
        decreases n
      {
        n := n / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    // If n > 1, then n is a prime factor
    if n > 1 {
      s := s + n;
    }
    
    // Check if we've reached a fixed point
    if s == t {
      if t <= 1000000000 {
        return t;
      } else {
        return n0;  // Fallback to original input
      }
    }
    
    if s >= 2 {
      n := s;
    } else {
      n := 2;  // Ensure n stays >= 2
    }
    iterations := iterations + 1;
  }
  
  // Fallback (should not reach here for valid inputs)
  return n0;
}

method digitToInt(c: char) returns (digit: int)
  requires '0' <= c <= '9'
  ensures 0 <= digit <= 9
  ensures digit == (c as int) - ('0' as int)
{
  digit := (c as int) - ('0' as int);
}

method intToChar(digit: int) returns (c: char)
  requires 0 <= digit <= 9
  ensures '0' <= c <= '9'
  ensures c == (digit + ('0' as int)) as char
{
  c := (digit + ('0' as int)) as char;
}

method stringToInt(s: string) returns (result: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures result >= 0
{
  result := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
  {
    var digit := digitToInt(s[i]);
    result := result * 10 + digit;
    i := i + 1;
  }
}

method intToString(n: int) returns (s: string)
  requires n >= 0
  ensures |s| > 0
  ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if n == 0 {
    s := "0";
    return;
  }
  
  var digits: seq<char> := [];
  var temp := n;
  
  while temp > 0
    invariant temp >= 0
    invariant |digits| >= 0
    invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    invariant temp == 0 ==> |digits| > 0
    decreases temp
  {
    var digit := temp % 10;
    var c := intToChar(digit);
    digits := [c] + digits;
    temp := temp / 10;
  }
  
  s := digits;
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures result >= 0
{
  if n == 0 {
    return 0;
  }
  
  var s := intToString(n);
  var digits := s;
  var i := 1;
  
  // Find first position where digits are not increasing
  while i < |digits| && digits[i-1] <= digits[i]
    invariant 1 <= i <= |digits|
    invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
  {
    i := i + 1;
  }
  
  // If we found a decreasing position, fix it
  if i < |digits| {
    // Decrease digits and propagate backwards
    while i > 0 && i < |digits| && digits[i-1] > digits[i]
      invariant 0 <= i < |digits|
      invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
    {
      var prevDigit := digitToInt(digits[i-1]);
      if prevDigit > 0 {
        var newChar := intToChar(prevDigit - 1);
        digits := digits[i-1 := newChar];
      }
      i := i - 1;
    }
    
    // Set all following digits to '9'
    i := i + 1;
    while i < |digits|
      invariant 0 <= i <= |digits|
      invariant forall j :: 0 <= j < |digits| ==> '0' <= digits[j] <= '9'
    {
      digits := digits[i := '9'];
      i := i + 1;
    }
  }
  
  result := stringToInt(digits);
}

method main_2node_1(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result >= 0
{
  var o1 := smallestValue_2507(o);
  var o2 := monotoneIncreasingDigits_738(o1);
  result := o2;
}
