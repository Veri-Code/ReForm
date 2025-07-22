
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
  while i >= 2
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
      if mul > 100000000 { // Prevent overflow
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

method countDigits(n: int) returns (evenCount: int, oddCount: int, totalCount: int)
  requires n >= 0
  ensures evenCount >= 0 && oddCount >= 0 && totalCount >= 0
  ensures evenCount + oddCount == totalCount
  ensures n == 0 ==> totalCount == 1
  ensures n > 0 ==> totalCount > 0
{
  var t := n;
  evenCount := 0;
  oddCount := 0;
  totalCount := 0;
  
  if t == 0 {
    evenCount := 1; // 0 is even
    totalCount := 1;
    return;
  }
  
  while t > 0
    invariant t >= 0
    invariant evenCount >= 0 && oddCount >= 0 && totalCount >= 0
    invariant evenCount + oddCount == totalCount
    invariant t == 0 ==> totalCount > 0
    decreases t
  {
    var digit := t % 10;
    if digit % 2 == 0 {
      evenCount := evenCount + 1;
    } else {
      oddCount := oddCount + 1;
    }
    totalCount := totalCount + 1;
    t := t / 10;
  }
}

method power10(exp: int) returns (result: int)
  requires 0 <= exp <= 10
  ensures result > 0
{
  result := 1;
  var i := 0;
  while i < exp
    invariant 0 <= i <= exp
    invariant result > 0
    decreases exp - i
  {
    result := result * 10;
    i := i + 1;
  }
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 0 <= result <= 1000000000
  decreases 1000000000 - n
{
  var evenCount, oddCount, totalCount := countDigits(n);
  
  if totalCount % 2 == 1 {
    // Odd number of digits, need to go to next even-digit number
    if totalCount <= 10 {
      var x := power10(totalCount);
      var halfDigits := totalCount / 2;
      var y := 0;
      if halfDigits > 0 {
        var temp := power10(halfDigits);
        y := (temp - 1) / 9; // This gives us halfDigits number of 1's
      }
      result := x + y;
      if result > 1000000000 {
        result := 1000000000;
      }
    } else {
      result := 1000000000;
    }
    return result;
  }
  
  if evenCount == oddCount {
    return n;
  }
  
  if n < 1000000000 {
    result := closestFair_2417(n + 1);
  } else {
    result := 1000000000;
  }
}

method digitToInt(c: char) returns (digit: int)
  requires '0' <= c <= '9'
  ensures 0 <= digit <= 9
{
  digit := (c as int) - ('0' as int);
}

method intToChar(digit: int) returns (c: char)
  requires 0 <= digit <= 9
  ensures '0' <= c <= '9'
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
    decreases |s| - i
  {
    var digit := digitToInt(s[i]);
    result := result * 10 + digit;
    i := i + 1;
  }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures result >= 0
{
  if n == 0 {
    return 0;
  }
  
  var s := [];
  var temp := n;
  
  // Convert number to array of digits
  while temp > 0
    invariant temp >= 0
    invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    decreases temp
  {
    var digit := temp % 10;
    s := [digit] + s;
    temp := temp / 10;
  }
  
  if |s| == 0 {
    return 0;
  }
  
  var i := 1;
  while i < |s| && s[i-1] <= s[i]
    invariant 1 <= i <= |s|
    decreases |s| - i
  {
    i := i + 1;
  }
  
  if i < |s| {
    while i > 0 && i < |s| && s[i-1] > s[i]
      invariant 0 <= i < |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
      decreases i
    {
      if s[i-1] > 0 {
        s := s[i-1 := s[i-1] - 1];
      }
      i := i - 1;
    }
    i := i + 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
      decreases |s| - i
    {
      s := s[i := 9];
      i := i + 1;
    }
  }
  
  // Convert back to integer
  result := 0;
  i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
    invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    decreases |s| - i
  {
    if result <= 214748364 && (result < 214748364 || s[i] <= 7) {
      result := result * 10 + s[i];
    }
    i := i + 1;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 0
{
  var o1 := smallestFactorization_625(o);
  if o1 == 0 {
    result := 0;
    return;
  }
  var o2 := closestFair_2417(o1);
  var o3 := monotoneIncreasingDigits_738(o2);
  result := o3;
}
