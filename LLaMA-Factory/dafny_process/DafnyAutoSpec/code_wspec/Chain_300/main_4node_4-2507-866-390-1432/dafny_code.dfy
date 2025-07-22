
function reverse(x: int): int
  requires x >= 0
  ensures reverse(x) >= 0
{
  if x == 0 then 0
  else reverse(x / 10) * 10 + x % 10
}

function is_prime(x: int): bool
  requires x >= 0
{
  if x < 2 then false
  else is_prime_helper(x, 2)
}

function is_prime_helper(x: int, v: int): bool
  requires x >= 2
  requires v >= 2
  decreases x - v * v + 1
{
  if v * v > x then true
  else if x % v == 0 then false
  else is_prime_helper(x, v + 1)
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 100000000
  decreases *
{
  var current := n;
  while true
    decreases *
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp := current;
    
    // Factor the number and sum the prime factors
    while i * i <= temp && temp > 1
      invariant 2 <= i
      invariant s >= 0
      invariant temp >= 1
      invariant t >= 2
      decreases temp - i + 1
    {
      while temp % i == 0 && temp > 1
        invariant temp >= 1
        invariant i >= 2
        invariant s >= 0
        decreases temp
      {
        temp := temp / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    // Add remaining prime factor if > 1
    if temp > 1 {
      s := s + temp;
    }
    
    // If sum equals original, we found the answer
    if s == t {
      assert t >= 2;
      if t <= 100000000 {
        return t;
      } else {
        return 100000000;
      }
    }
    
    current := s;
    if current <= 1 {
      return 1;
    }
  }
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures 1 <= result <= 1000000000
  decreases *
{
  var current := n;
  while true
    decreases *
  {
    if current >= 1 && current <= 1000000000 && reverse(current) == current && is_prime(current) {
      return current;
    }
    
    // Skip even-digit palindromes except 11 (optimization from original)
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
    
    if current > 1000000000 {
      return 1000000000;
    }
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 100000000
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant 1 <= a1
    invariant an >= 0
    decreases cnt
  {
    if i % 2 == 1 {
      if an >= step {
        an := an - step;
      } else {
        an := 0;
      }
      if cnt % 2 == 1 {
        a1 := a1 + step;
      }
    } else {
      a1 := a1 + step;
      if cnt % 2 == 1 {
        if an >= step {
          an := an - step;
        } else {
          an := 0;
        }
      }
    }
    cnt := cnt / 2;
    step := step * 2;
    i := i + 1;
  }
  
  if a1 <= 100000000 {
    return a1;
  } else {
    return 100000000;
  }
}

method maxDiff_1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000
  ensures result >= 0
{
  // Convert to string representation conceptually
  var digits := getDigits(num);
  var maxNum := makeMaxNumber(digits);
  var minNum := makeMinNumber(digits);
  
  // Ensure the result is non-negative
  if maxNum >= minNum {
    return maxNum - minNum;
  } else {
    return 0;
  }
}

method getDigits(num: int) returns (digits: seq<int>)
  requires num >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var temp := num;
  var result: seq<int> := [];
  
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
    decreases temp
  {
    result := [temp % 10] + result;
    temp := temp / 10;
  }
  
  if |result| == 0 {
    result := [0];
  }
  
  return result;
}

method makeMaxNumber(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  // Find first digit that's not 9 and replace all occurrences with 9
  var maxDigits := digits;
  var i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
  {
    if digits[i] != 9 {
      maxDigits := replaceDigit(digits, digits[i], 9);
      break;
    }
    i := i + 1;
  }
  
  var maxNum := digitsToNumber(maxDigits);
  return maxNum;
}

method makeMinNumber(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  var minDigits := digits;
  
  // If first digit is not 1, replace all occurrences with 1
  if digits[0] != 1 {
    minDigits := replaceDigit(digits, digits[0], 1);
  } else {
    // Find first digit after position 0 that's not 0 or 1
    var i := 1;
    while i < |digits|
      invariant 1 <= i <= |digits|
    {
      if digits[i] != 0 && digits[i] != 1 {
        minDigits := replaceDigit(digits, digits[i], 0);
        break;
      }
      i := i + 1;
    }
  }
  
  var minNum := digitsToNumber(minDigits);
  return minNum;
}

method replaceDigit(digits: seq<int>, oldDigit: int, newDigit: int) returns (result: seq<int>)
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires 0 <= oldDigit <= 9
  requires 0 <= newDigit <= 9
  ensures |result| == |digits|
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
{
  var newDigits: seq<int> := [];
  var i := 0;
  
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant |newDigits| == i
    invariant forall j :: 0 <= j < i ==> 0 <= newDigits[j] <= 9
  {
    if digits[i] == oldDigit {
      newDigits := newDigits + [newDigit];
    } else {
      newDigits := newDigits + [digits[i]];
    }
    i := i + 1;
  }
  
  return newDigits;
}

method digitsToNumber(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  var num := 0;
  var i := 0;
  
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant num >= 0
  {
    num := num * 10 + digits[i];
    i := i + 1;
  }
  
  return num;
}

method main_4node_4(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result >= 0
  decreases *
{
  var o1 := smallestValue_2507(o);
  var o2 := primePalindrome_866(o1);
  var o3 := lastRemaining_390(o2);
  var o4 := maxDiff_1432(o3);
  return o4;
}
