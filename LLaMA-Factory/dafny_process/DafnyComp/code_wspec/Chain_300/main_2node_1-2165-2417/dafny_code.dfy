
method abs(x: int) returns (result: int)
  ensures result >= 0
  ensures result == if x >= 0 then x else -x
{
  if x >= 0 {
    result := x;
  } else {
    result := -x;
  }
}

method countDigits(num: int) returns (cnt: array<int>, digitCount: int)
  requires num >= 0
  ensures cnt.Length == 10
  ensures digitCount >= 1
  ensures forall i :: 0 <= i < 10 ==> cnt[i] >= 0
  ensures digitCount <= 16
  ensures fresh(cnt)
  modifies {}
{
  cnt := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant forall j :: 0 <= j < i ==> cnt[j] == 0
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var n := num;
  digitCount := 0;
  
  if n == 0 {
    cnt[0] := 1;
    digitCount := 1;
    return;
  }
  
  while n > 0
    invariant n >= 0
    invariant digitCount >= 0
    invariant forall j :: 0 <= j < 10 ==> cnt[j] >= 0
    decreases n
  {
    var digit := n % 10;
    cnt[digit] := cnt[digit] + 1;
    n := n / 10;
    digitCount := digitCount + 1;
  }
  
  if digitCount == 0 {
    digitCount := 1;
  }
  if digitCount > 16 {
    digitCount := 16;
  }
}

method power10(exp: int) returns (result: int)
  requires 0 <= exp <= 15
  ensures result > 0
{
  result := 1;
  var i := 0;
  while i < exp
    invariant 0 <= i <= exp
    invariant result > 0
  {
    result := result * 10;
    i := i + 1;
  }
}

method smallestNumber_2165(num: int) returns (result: int)
  requires -1000000000000000 <= num <= 1000000000000000
  ensures 1 <= result <= 1000000000
  modifies {}
{
  var neg := num < 0;
  var absNum := abs(num);
  var cnt, digitCount := countDigits(absNum);
  
  var ans := 0;
  
  if neg {
    var i := 9;
    while i >= 0
      invariant -1 <= i <= 9
      invariant ans >= 0
      modifies cnt
    {
      var j := 0;
      while j < cnt[i]
        invariant 0 <= j <= cnt[i]
        invariant ans >= 0
        modifies cnt
      {
        ans := ans * 10 + i;
        j := j + 1;
      }
      i := i - 1;
    }
    result := if ans == 0 then 1 else ans;
  } else {
    if cnt[0] > 0 {
      var i := 1;
      while i < 10
        invariant 1 <= i <= 10
        modifies cnt
      {
        if cnt[i] > 0 {
          ans := i;
          cnt[i] := cnt[i] - 1;
          break;
        }
        i := i + 1;
      }
    }
    
    var i := 0;
    while i < 10
      invariant 0 <= i <= 10
      invariant ans >= 0
      modifies cnt
    {
      var j := 0;
      while j < cnt[i]
        invariant 0 <= j <= cnt[i]
        invariant ans >= 0
        modifies cnt
      {
        ans := ans * 10 + i;
        j := j + 1;
      }
      i := i + 1;
    }
    
    result := if ans == 0 then 1 else ans;
  }
  
  if result < 1 {
    result := 1;
  }
  if result > 1000000000 {
    result := 1000000000;
  }
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures result >= 1
  decreases 1000000000 - n
{
  var a := 0;
  var b := 0;
  var k := 0;
  var t := n;
  
  while t > 0
    invariant t >= 0
    invariant a >= 0 && b >= 0 && k >= 0
    invariant a + b == k
    decreases t
  {
    if (t % 10) % 2 == 1 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    t := t / 10;
    k := k + 1;
  }
  
  if k % 2 == 1 {
    if k <= 15 {
      var x := power10(k);
      var halfK := k / 2;
      var y := 0;
      if halfK > 0 {
        var i := 0;
        y := 1;
        while i < halfK - 1
          invariant 0 <= i <= halfK - 1
          invariant y > 0
        {
          y := y * 10 + 1;
          i := i + 1;
        }
      }
      result := x + y;
    } else {
      result := n;
    }
  } else if a == b {
    result := n;
  } else {
    if n < 1000000000 {
      result := closestFair_2417(n + 1);
    } else {
      result := n;
    }
  }
}

method main_2node_1(o: int) returns (result: int)
  requires -1000000000000000 <= o <= 1000000000000000
  ensures 1 <= result
{
  var o1 := smallestNumber_2165(o);
  var o2 := closestFair_2417(o1);
  result := o2;
}
