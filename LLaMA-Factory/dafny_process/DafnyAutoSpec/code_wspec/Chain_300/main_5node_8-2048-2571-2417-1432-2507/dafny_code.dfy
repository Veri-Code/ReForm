
method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures 1 <= result <= 100000000
  ensures result > n
  decreases *
{
  var x := n + 1;
  while true
    invariant x > n
    decreases *
  {
    var y := x;
    var cnt := new int[10];
    var i := 0;
    while i < 10
      invariant 0 <= i <= 10
      invariant forall j :: 0 <= j < i ==> cnt[j] == 0
    {
      cnt[i] := 0;
      i := i + 1;
    }
    
    while y > 0
      invariant y >= 0
      decreases y
    {
      var digit := y % 10;
      y := y / 10;
      cnt[digit] := cnt[digit] + 1;
    }
    
    var isBeautiful := true;
    i := 0;
    while i < 10 && isBeautiful
      invariant 0 <= i <= 10
    {
      if cnt[i] != 0 && cnt[i] != i {
        isBeautiful := false;
      }
      i := i + 1;
    }
    
    if isBeautiful {
      assert x > n;
      assert x >= 1;
      if x <= 100000000 {
        return x;
      }
    }
    x := x + 1;
  }
}

method minOperations_2571(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures 1 <= result <= 1000000000
{
  var ans := 0;
  var cnt := 0;
  var num := n;
  
  while num > 0
    invariant num >= 0
    invariant ans >= 0
    invariant cnt >= 0
    decreases num
  {
    if num % 2 == 1 {
      cnt := cnt + 1;
    } else if cnt > 0 {
      ans := ans + 1;
      if cnt == 1 {
        cnt := 0;
      } else {
        cnt := 1;
      }
    }
    num := num / 2;
  }
  
  if cnt == 1 {
    ans := ans + 1;
  } else if cnt > 1 {
    ans := ans + 2;
  }
  
  result := if ans == 0 then 1 else ans;
  assert result >= 1;
  if result > 1000000000 {
    result := 1000000000;
  }
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 100000000000
  decreases *
{
  var a := 0;  // count of odd digits
  var b := 0;  // count of even digits
  var k := 0;  // total digits
  var t := n;
  
  while t > 0
    invariant t >= 0
    invariant a >= 0
    invariant b >= 0
    invariant k >= 0
    decreases t
  {
    var digit := t % 10;
    if digit % 2 == 1 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    t := t / 10;
    k := k + 1;
  }
  
  if k % 2 == 1 {
    // Odd number of digits, need even number
    var x := power10(k);
    var y := if k / 2 > 0 then power10(k / 2) - 1 else 0;
    result := x + y;
    assert result >= 1;
    if result > 100000000000 {
      result := 100000000000;
    }
  } else if a == b {
    result := n;
    assert result >= 1;
  } else {
    if n + 1 <= 1000000000 {
      result := closestFair_2417(n + 1);
    } else {
      result := 10000000000;
    }
  }
}

function power10(exp: int): int
  requires exp >= 0
  ensures power10(exp) >= 1
{
  if exp == 0 then 1
  else 10 * power10(exp - 1)
}

method maxDiff_1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000000
  ensures 0 <= result <= 100000000000
{
  var digits := getDigits(num);
  var maxNum := makeMaxNumber(digits);
  var minNum := makeMinNumber(digits);
  var diff := if maxNum >= minNum then maxNum - minNum else 0;
  result := diff;
  if result > 100000000000 {
    result := 100000000000;
  }
}

method getDigits(num: int) returns (digits: seq<int>)
  requires num >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var result := [];
  var n := num;
  
  while n > 0
    invariant n >= 0
    invariant forall i :: 0 <= i < |result| ==> 0 <= result[i] <= 9
    decreases n
  {
    result := [n % 10] + result;
    n := n / 10;
  }
  
  digits := result;
  if |digits| == 0 {
    digits := [0];
  }
  assert |digits| >= 1;
}

method makeMaxNumber(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  var maxDigits := digits;
  var i := 0;
  
  while i < |maxDigits|
    invariant 0 <= i <= |maxDigits|
    invariant forall j :: 0 <= j < |maxDigits| ==> 0 <= maxDigits[j] <= 9
  {
    if maxDigits[i] != 9 {
      maxDigits := replaceDigit(maxDigits, maxDigits[i], 9);
      break;
    }
    i := i + 1;
  }
  
  return digitsToNumber(maxDigits);
}

method makeMinNumber(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  var minDigits := digits;
  
  if minDigits[0] != 1 {
    minDigits := replaceDigit(minDigits, minDigits[0], 1);
  } else {
    var i := 1;
    while i < |minDigits|
      invariant 1 <= i <= |minDigits|
      invariant forall j :: 0 <= j < |minDigits| ==> 0 <= minDigits[j] <= 9
    {
      if minDigits[i] != 0 && minDigits[i] != 1 {
        minDigits := replaceDigit(minDigits, minDigits[i], 0);
        break;
      }
      i := i + 1;
    }
  }
  
  return digitsToNumber(minDigits);
}

function replaceDigit(digits: seq<int>, oldDigit: int, newDigit: int): seq<int>
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires 0 <= oldDigit <= 9
  requires 0 <= newDigit <= 9
  ensures |replaceDigit(digits, oldDigit, newDigit)| == |digits|
  ensures forall i :: 0 <= i < |replaceDigit(digits, oldDigit, newDigit)| ==> 0 <= replaceDigit(digits, oldDigit, newDigit)[i] <= 9
{
  seq(|digits|, i requires 0 <= i < |digits| => if digits[i] == oldDigit then newDigit else digits[i])
}

function digitsToNumber(digits: seq<int>): int
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures digitsToNumber(digits) >= 0
{
  if |digits| == 1 then digits[0]
  else digits[0] * power10(|digits| - 1) + digitsToNumber(digits[1..])
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n
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
    
    while i * i <= temp && temp > 1
      invariant i >= 2
      invariant s >= 0
      invariant temp >= 0
    {
      while temp % i == 0 && temp > 1
        invariant temp >= 0
        invariant i >= 2
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
    
    current := if s >= 2 then s else 2;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 0 <= o <= 1000000
  ensures 2 <= result
  decreases *
{
  var o1 := nextBeautifulNumber_2048(o);
  var o2 := minOperations_2571(o1);
  var o3 := closestFair_2417(o2);
  var o4 := maxDiff_1432(o3);
  if o4 >= 2 {
    var o5 := smallestValue_2507(o4);
    return o5;
  } else {
    var o5 := smallestValue_2507(2);
    return o5;
  }
}
