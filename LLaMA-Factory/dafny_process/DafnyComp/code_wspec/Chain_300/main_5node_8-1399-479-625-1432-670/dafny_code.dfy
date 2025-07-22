
method digitSum(n: int) returns (sum: int)
  requires n >= 0
  ensures sum >= 0
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
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 8
{
  var cnt := new int[82];
  var i := 0;
  while i < cnt.Length
    invariant 0 <= i <= cnt.Length
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var mx := 0;
  var ans := 0;
  
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant mx >= 0
    invariant ans >= 0
  {
    var s := digitSum(i);
    if s < cnt.Length {
      cnt[s] := cnt[s] + 1;
      if mx < cnt[s] {
        mx := cnt[s];
        ans := 1;
      } else if mx == cnt[s] {
        ans := ans + 1;
      }
    }
    i := i + 1;
  }
  
  result := if ans == 0 then 1 else ans;
  assert result >= 1;
  if result > 8 {
    result := 8;
  }
}

method reverseDigits(a: int) returns (result: int)
  requires a >= 0
  ensures result >= 0
{
  var b := a;
  var x := a;
  while b > 0
    invariant b >= 0
    invariant x >= 0
  {
    x := x * 10 + (b % 10);
    b := b / 10;
  }
  result := x;
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 2147483648
{
  if n == 1 {
    result := 9;
    return;
  }
  
  var mx := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant mx >= 1
  {
    mx := mx * 10;
    i := i + 1;
  }
  mx := mx - 1;
  
  var a := mx;
  while a > mx / 10
    invariant a >= 0
  {
    var x := reverseDigits(a);
    var t := mx;
    while t * t >= x && t > 0
      invariant t >= 0
    {
      if x % t == 0 {
        result := x % 1337;
        if result == 0 {
          result := 1;
        }
        return;
      }
      t := t - 1;
    }
    a := a - 1;
  }
  
  result := 9;
}

method smallestFactorization_625(num: int) returns (result: int)
  requires 1 <= num <= 2147483648
  ensures 0 <= result <= 2147483647
{
  if num < 2 {
    result := num;
    return;
  }
  
  var n := num;
  var ans := 0;
  var mul := 1;
  
  var i := 9;
  while i >= 2
    invariant 1 <= i <= 9
    invariant ans >= 0
    invariant mul >= 1
    invariant n >= 1
  {
    while n % i == 0 && mul <= 100000000
      invariant n >= 1
      invariant mul >= 1
      invariant ans >= 0
    {
      n := n / i;
      ans := mul * i + ans;
      mul := mul * 10;
    }
    i := i - 1;
  }
  
  if n < 2 && ans <= 2147483647 {
    result := ans;
  } else {
    result := 0;
  }
}

method intToString(num: int) returns (s: string)
  requires num >= 0
  ensures |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if num == 0 {
    s := "0";
    return;
  }
  
  var digits := [];
  var n := num;
  while n > 0
    invariant n >= 0
    invariant |digits| >= 0
    invariant n == 0 ==> |digits| >= 1
  {
    digits := [n % 10] + digits;
    n := n / 10;
  }
  
  s := "";
  var i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant |s| == i
    invariant forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
  {
    var digit := digits[i];
    var digitChar := if digit == 0 then '0'
                    else if digit == 1 then '1'
                    else if digit == 2 then '2'
                    else if digit == 3 then '3'
                    else if digit == 4 then '4'
                    else if digit == 5 then '5'
                    else if digit == 6 then '6'
                    else if digit == 7 then '7'
                    else if digit == 8 then '8'
                    else '9';
    s := s + [digitChar];
    i := i + 1;
  }
}

method stringToInt(s: string) returns (num: int)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures num >= 0
{
  num := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant num >= 0
  {
    var digitVal := s[i] as int - '0' as int;
    num := num * 10 + digitVal;
    i := i + 1;
  }
}

method maxDiff_1432(num: int) returns (result: int)
  requires 1 <= num <= 100000000
  ensures 0 <= result <= 999999999
{
  var s := intToString(num);
  var a := s;
  var b := s;
  
  // Maximize a by replacing first non-'9' with '9'
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |a| ==> '0' <= a[j] <= '9'
  {
    if a[i] != '9' {
      var newA := "";
      var j := 0;
      while j < |a|
        invariant 0 <= j <= |a|
        invariant |newA| == j
        invariant forall k :: 0 <= k < |newA| ==> '0' <= newA[k] <= '9'
      {
        if a[j] == a[i] {
          newA := newA + ['9'];
        } else {
          newA := newA + [a[j]];
        }
        j := j + 1;
      }
      a := newA;
      break;
    }
    i := i + 1;
  }
  
  // Minimize b
  if |b| > 0 && b[0] != '1' {
    var newB := "";
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant |newB| == j
      invariant forall k :: 0 <= k < |newB| ==> '0' <= newB[k] <= '9'
    {
      if b[j] == b[0] {
        newB := newB + ['1'];
      } else {
        newB := newB + [b[j]];
      }
      j := j + 1;
    }
    b := newB;
  } else {
    i := 1;
    while i < |b|
      invariant 1 <= i <= |b|
      invariant forall j :: 0 <= j < |b| ==> '0' <= b[j] <= '9'
    {
      if b[i] != '0' && b[i] != '1' {
        var newB := "";
        var j := 0;
        while j < |b|
          invariant 0 <= j <= |b|
          invariant |newB| == j
          invariant forall k :: 0 <= k < |newB| ==> '0' <= newB[k] <= '9'
        {
          if b[j] == b[i] {
            newB := newB + ['0'];
          } else {
            newB := newB + [b[j]];
          }
          j := j + 1;
        }
        b := newB;
        break;
      }
      i := i + 1;
    }
  }
  
  var maxVal := stringToInt(a);
  var minVal := stringToInt(b);
  result := maxVal - minVal;
  
  if result < 0 {
    result := 0;
  }
  if result > 999999999 {
    result := 999999999;
  }
}

method maximumSwap_670(num: int) returns (result: int)
  requires 0 <= num <= 999999999
  ensures result >= 0
{
  var s := intToString(num);
  var digits := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |digits| == i
    invariant forall j :: 0 <= j < i ==> 0 <= digits[j] <= 9
  {
    digits := digits + [s[i] as int - '0' as int];
    i := i + 1;
  }
  
  var n := |digits|;
  if n == 0 {
    result := 0;
    return;
  }
  
  var d := [];
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |d| == i
    invariant forall j :: 0 <= j < i ==> 0 <= d[j] < n
  {
    d := d + [i];
    i := i + 1;
  }
  
  i := n - 2;
  while i >= 0
    invariant -1 <= i <= n - 2
    invariant |d| == n
    invariant forall j :: 0 <= j < |d| ==> 0 <= d[j] < n
  {
    if i + 1 < |d| && digits[i] <= digits[d[i + 1]] {
      d := d[i := d[i + 1]];
    }
    i := i - 1;
  }
  
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |d| == n
    invariant |digits| == n
    invariant forall j :: 0 <= j < |d| ==> 0 <= d[j] < n
    invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
  {
    var j := d[i];
    if digits[i] < digits[j] {
      var temp := digits[i];
      digits := digits[i := digits[j]];
      digits := digits[j := temp];
      break;
    }
    i := i + 1;
  }
  
  result := 0;
  i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant result >= 0
    invariant forall j :: 0 <= j < |digits| ==> 0 <= digits[j] <= 9
  {
    result := result * 10 + digits[i];
    i := i + 1;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures result >= 0
{
  var o1 := countLargestGroup_1399(o);
  var o2 := largestPalindrome_479(o1);
  var o3 := smallestFactorization_625(o2);
  if o3 >= 1 && o3 <= 100000000 {
    var o4 := maxDiff_1432(o3);
    if o4 <= 999999999 {
      var o5 := maximumSwap_670(o4);
      result := o5;
    } else {
      result := 0;
    }
  } else {
    result := 0;
  }
}
