
method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures true
{
  var o1 := maxDiff_1432(o);
  var o2 := distinctSequences_2318(o1);
  var o3 := clumsy_1006(o2);
  result := o3;
}

method maxDiff_1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000
  ensures 1 <= result <= 10000
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
      var target := maxDigits[i];
      var j := 0;
      while j < |maxDigits|
        invariant 0 <= j <= |maxDigits|
        invariant |maxDigits| == |digits|
        invariant forall k :: 0 <= k < |maxDigits| ==> 0 <= maxDigits[k] <= 9
      {
        if maxDigits[j] == target {
          maxDigits := maxDigits[j := 9];
        }
        j := j + 1;
      }
      break;
    }
    i := i + 1;
  }
  
  // Minimize: replace first digit with 1, or first non-0/1 after leading 1 with 0
  if |minDigits| > 0 {
    if minDigits[0] != 1 {
      var target := minDigits[0];
      var j := 0;
      while j < |minDigits|
        invariant 0 <= j <= |minDigits|
        invariant |minDigits| == |digits|
        invariant forall k :: 0 <= k < |minDigits| ==> 0 <= minDigits[k] <= 9
      {
        if minDigits[j] == target {
          minDigits := minDigits[j := 1];
        }
        j := j + 1;
      }
    } else {
      var k := 1;
      while k < |minDigits|
        invariant 1 <= k <= |minDigits|
        invariant |minDigits| == |digits|
        invariant forall m :: 0 <= m < |minDigits| ==> 0 <= minDigits[m] <= 9
      {
        if minDigits[k] != 0 && minDigits[k] != 1 {
          var target := minDigits[k];
          var j := 0;
          while j < |minDigits|
            invariant 0 <= j <= |minDigits|
            invariant |minDigits| == |digits|
            invariant forall m :: 0 <= m < |minDigits| ==> 0 <= minDigits[m] <= 9
          {
            if minDigits[j] == target {
              minDigits := minDigits[j := 0];
            }
            j := j + 1;
          }
          break;
        }
        k := k + 1;
      }
    }
  }
  
  var maxNum := digitsToInt(maxDigits);
  var minNum := digitsToInt(minDigits);
  result := maxNum - minNum;
  
  // Bound the result
  if result > 10000 {
    result := 10000;
  }
  if result < 1 {
    result := 1;
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 10000
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize dp[2][i][j]
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      if gcd(i + 1, j + 1) == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill dp table
  var k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
      {
        if gcd(i + 1, j + 1) == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
          {
            if gcd(h + 1, i + 1) == 1 && h != i && h != j {
              dp[k, i, j] := (dp[k, i, j] + dp[k - 1, h, i]) % mod;
            }
            h := h + 1;
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Sum all dp[n][i][j]
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant 0 <= ans < mod
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant 0 <= ans < mod
    {
      ans := (ans + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := ans;
  if result == 0 {
    result := 1;
  }
  if result > 10000 {
    result := result % 10000;
    if result == 0 {
      result := 10000;
    }
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures true
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant |stk| >= 1
    invariant 0 <= k <= 3
  {
    if k == 0 {
      var top := stk[|stk| - 1];
      stk := stk[..|stk| - 1] + [top * x];
    } else if k == 1 {
      var top := stk[|stk| - 1];
      stk := stk[..|stk| - 1] + [top / x];
    } else if k == 2 {
      stk := stk + [x];
    } else {
      stk := stk + [-x];
    }
    k := (k + 1) % 4;
    x := x - 1;
  }
  
  result := sumSeq(stk);
}

// Helper methods
method intToDigits(n: int) returns (digits: seq<int>)
  requires n >= 1
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  digits := [];
  var temp := n;
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    decreases temp
  {
    var digit := temp % 10;
    assert 0 <= digit <= 9;
    digits := [digit] + digits;
    temp := temp / 10;
  }
  
  if |digits| == 0 {
    digits := [0];
  }
}

method digitsToInt(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
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

function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function sumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sumSeq(s[1..])
}
