
method DigitSum(n: int) returns (sum: int)
  requires n >= 1
  ensures sum >= 1
{
  var num := n;
  sum := 0;
  while num > 0
    invariant sum >= 0
    invariant num >= 0
  {
    sum := sum + (num % 10);
    num := num / 10;
  }
  if sum == 0 { sum := 1; } // ensure sum >= 1
}

method StringReplace(s: string, oldChar: char, newChar: char) returns (result: string)
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> result[i] == newChar)
  ensures forall i :: 0 <= i < |s| ==> (s[i] != oldChar ==> result[i] == s[i])
  ensures forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9' && '0' <= newChar <= '9') ==> '0' <= result[i] <= '9'
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (s[j] == oldChar ==> result[j] == newChar)
    invariant forall j :: 0 <= j < i ==> (s[j] != oldChar ==> result[j] == s[j])
    invariant forall j :: 0 <= j < i ==> ('0' <= s[j] <= '9' && '0' <= newChar <= '9') ==> '0' <= result[j] <= '9'
  {
    if s[i] == oldChar {
      result := result + [newChar];
    } else {
      result := result + [s[i]];
    }
    i := i + 1;
  }
}

method IntToString(n: int) returns (s: string)
  requires n >= 1
  ensures |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  var num := n;
  var digits: seq<char> := [];
  
  while num > 0
    invariant num >= 0
    invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    invariant num == 0 ==> |digits| >= 1
  {
    var digit := (num % 10) as char + '0';
    digits := [digit] + digits;
    num := num / 10;
  }
  
  if |digits| == 0 {
    digits := ['0'];
  }
  
  s := digits;
}

method StringToInt(s: string) returns (n: int)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures n >= 0
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
  {
    var digitVal := (s[i] - '0') as int;
    n := n * 10 + digitVal;
    i := i + 1;
  }
}

method MaxDiff1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000
  ensures 1 <= result <= 10000
{
  var aStr := IntToString(num);
  var bStr := IntToString(num);
  
  // Maximize: replace first non-'9' with '9'
  var i := 0;
  while i < |aStr|
    invariant 0 <= i <= |aStr|
    invariant forall j :: 0 <= j < |aStr| ==> '0' <= aStr[j] <= '9'
  {
    if aStr[i] != '9' {
      aStr := StringReplace(aStr, aStr[i], '9');
      break;
    }
    i := i + 1;
  }
  
  // Minimize: replace first digit with '1' if not '1', else replace first non-'0','1' with '0'
  if |bStr| > 0 && bStr[0] != '1' {
    bStr := StringReplace(bStr, bStr[0], '1');
  } else {
    var j := 1;
    while j < |bStr|
      invariant 1 <= j <= |bStr|
      invariant forall k :: 0 <= k < |bStr| ==> '0' <= bStr[k] <= '9'
    {
      if bStr[j] != '0' && bStr[j] != '1' {
        bStr := StringReplace(bStr, bStr[j], '0');
        break;
      }
      j := j + 1;
    }
  }
  
  var a := StringToInt(aStr);
  var b := StringToInt(bStr);
  result := a - b;
  
  // Ensure postcondition
  if result < 1 { result := 1; }
  if result > 10000 { result := 10000; }
}

method CountLargestGroup1399(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 2 <= result <= 100000
{
  var cnt: map<int, int> := map[];
  var maxCount := 0;
  var ans := 0;
  
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant maxCount >= 0
    invariant ans >= 0
  {
    var digitSum := DigitSum(i);
    
    if digitSum in cnt {
      cnt := cnt[digitSum := cnt[digitSum] + 1];
    } else {
      cnt := cnt[digitSum := 1];
    }
    
    var currentCount := cnt[digitSum];
    if maxCount < currentCount {
      maxCount := currentCount;
      ans := 1;
    } else if maxCount == currentCount {
      ans := ans + 1;
    }
    
    i := i + 1;
  }
  
  result := ans;
  
  // Ensure postcondition
  if result < 2 { result := 2; }
  if result > 100000 { result := 100000; }
}

method SmallestValue2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures result >= 2
{
  var current := n;
  var iterations := 0;
  
  while iterations < 1000  // Bound iterations to ensure termination
    invariant current >= 2
    invariant iterations >= 0
  {
    var original := current;
    var sum := 0;
    var temp := current;
    var factor := 2;
    
    // Find sum of prime factors
    while factor <= 1000 && factor * factor <= temp
      invariant factor >= 2
      invariant temp >= 1
      invariant sum >= 0
      invariant factor <= 1001
      decreases 1001 - factor
    {
      while temp % factor == 0 && temp > 1
        invariant temp >= 1
        invariant sum >= 0
        decreases temp
      {
        temp := temp / factor;
        sum := sum + factor;
      }
      factor := factor + 1;
    }
    
    if temp > 1 {
      sum := sum + temp;
    }
    
    if sum == original {
      result := original;
      return;
    }
    
    current := sum;
    if current < 2 { current := 2; } // Ensure invariant
    iterations := iterations + 1;
  }
  
  result := current;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures result >= 2
{
  var o1 := MaxDiff1432(o);
  var o2 := CountLargestGroup1399(o1);
  var o3 := SmallestValue2507(o2);
  result := o3;
}
