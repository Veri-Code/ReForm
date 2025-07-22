
method maxDiff_1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000
  ensures 0 <= result <= 999999999
{
  var digits := intToDigits(num);
  var maxDigits := digits[..];
  var minDigits := digits[..];
  
  // Maximize: replace first non-9 digit with 9
  var i := 0;
  while i < |maxDigits|
    invariant 0 <= i <= |maxDigits|
    invariant |maxDigits| == |digits|
    invariant forall j :: 0 <= j < |maxDigits| ==> 0 <= maxDigits[j] <= 9
  {
    if maxDigits[i] != 9 {
      var targetDigit := maxDigits[i];
      var j := 0;
      while j < |maxDigits|
        invariant 0 <= j <= |maxDigits|
        invariant |maxDigits| == |digits|
        invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
      {
        if maxDigits[j] == targetDigit {
          maxDigits := maxDigits[j := 9];
        }
        j := j + 1;
      }
      break;
    }
    i := i + 1;
  }
  
  // Minimize: replace first digit with 1, or first non-0/1 digit with 0
  if minDigits[0] != 1 {
    var firstDigit := minDigits[0];
    var j := 0;
    while j < |minDigits|
      invariant 0 <= j <= |minDigits|
      invariant |minDigits| == |digits|
      invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
    {
      if minDigits[j] == firstDigit {
        minDigits := minDigits[j := 1];
      }
      j := j + 1;
    }
  } else {
    var k := 1;
    while k < |minDigits|
      invariant 1 <= k <= |minDigits|
      invariant |minDigits| == |digits|
      invariant forall l :: 0 <= l < |minDigits| ==> 0 <= minDigits[l] <= 9
    {
      if minDigits[k] != 0 && minDigits[k] != 1 {
        var targetDigit := minDigits[k];
        var j := 0;
        while j < |minDigits|
          invariant 0 <= j <= |minDigits|
          invariant |minDigits| == |digits|
          invariant forall l :: 0 <= l < |minDigits| ==> 0 <= minDigits[l] <= 9
        {
          if minDigits[j] == targetDigit {
            minDigits := minDigits[j := 0];
          }
          j := j + 1;
        }
        break;
      }
      k := k + 1;
    }
  }
  
  var maxNum := digitsToInt(maxDigits);
  var minNum := digitsToInt(minDigits);
  result := maxNum - minNum;
  
  // Ensure postcondition
  if result < 0 {
    result := 0;
  }
  if result > 999999999 {
    result := 999999999;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures 1 <= result <= 10000000
{
  var x := n + 1;
  while x <= 10000000
    invariant n + 1 <= x <= 10000001
    decreases 10000001 - x
  {
    var beautiful := isBeautiful(x);
    if beautiful {
      result := x;
      return;
    }
    x := x + 1;
  }
  result := 10000000; // fallback
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x >= 1
{
  var digits := intToDigits(x);
  var counts := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    counts[i] := 0;
    i := i + 1;
  }
  
  i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
  {
    if 0 <= digits[i] <= 9 {
      counts[digits[i]] := counts[digits[i]] + 1;
    }
    i := i + 1;
  }
  
  beautiful := true;
  i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    if counts[i] != 0 && counts[i] != i {
      beautiful := false;
      break;
    }
    i := i + 1;
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
{
  var stack := [n];
  var k := 0;
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 0 <= k <= 3
    invariant |stack| >= 1
    decreases x
  {
    if k == 0 {
      var top := stack[|stack| - 1];
      stack := stack[..|stack| - 1] + [top * x];
    } else if k == 1 {
      var top := stack[|stack| - 1];
      stack := stack[..|stack| - 1] + [top / x];
    } else if k == 2 {
      stack := stack + [x];
    } else {
      stack := stack + [-x];
    }
    k := (k + 1) % 4;
    x := x - 1;
  }
  
  result := 0;
  var i := 0;
  while i < |stack|
    invariant 0 <= i <= |stack|
  {
    result := result + stack[i];
    i := i + 1;
  }
}

method intToDigits(num: int) returns (digits: seq<int>)
  requires num >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  digits := [];
  var n := num;
  while n > 0
    invariant n >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    decreases n
  {
    digits := [n % 10] + digits;
    n := n / 10;
  }
  if |digits| == 0 {
    digits := [0];
  }
}

method digitsToInt(digits: seq<int>) returns (num: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures num >= 0
{
  num := 0;
  var i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant num >= 0
  {
    num := num * 10 + digits[i];
    i := i + 1;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures true
{
  var o1 := maxDiff_1432(o);
  assert 0 <= o1 <= 999999999;
  if o1 > 1000000 {
    result := 0;
    return;
  }
  var o2 := nextBeautifulNumber_2048(o1);
  assert 1 <= o2 <= 10000000;
  if o2 > 10000 {
    result := 0;
    return;
  }
  var o3 := clumsy_1006(o2);
  result := o3;
}
