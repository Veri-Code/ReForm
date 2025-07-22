
function gcd_func(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a
  else gcd_func(b, a % b)
}

lemma gcd_func_properties(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd_func(a, b) > 0
  ensures b > 0 ==> gcd_func(a, b) == gcd_func(b, a)
  decreases b
{
  if b == 0 {
  } else {
    gcd_func_properties(b, a % b);
    if a % b > 0 {
      gcd_func_properties(a % b, b % (a % b));
    }
  }
}

method gcd(a: int, b: int) returns (result: int)
  requires a > 0 && b > 0
  ensures result > 0
  ensures result == gcd_func(a, b)
{
  var x := a;
  var y := b;
  while y != 0
    invariant x > 0 && y >= 0
    invariant y == 0 ==> x == gcd_func(a, b)
    invariant y > 0 ==> gcd_func(a, b) == gcd_func(x, y)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

method digitSum(n: int) returns (sum: int)
  requires n >= 0
  ensures sum >= 0
{
  sum := 0;
  var num := n;
  while num > 0
    invariant num >= 0
    invariant sum >= 0
  {
    sum := sum + (num % 10);
    num := num / 10;
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 0
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize all values to 0
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      var k := 0;
      while k < 6
        invariant 0 <= k <= 6
      {
        dp[i, j, k] := 0;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Initialize base case for length 2
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      if i != j {
        var g := gcd(i + 1, j + 1);
        if g == 1 {
          dp[2, i, j] := 1;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill DP table for lengths 3 to n
  var len := 3;
  while len <= n
    invariant 3 <= len <= n + 1
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
      {
        if i != j {
          var g1 := gcd(i + 1, j + 1);
          if g1 == 1 {
            var h := 0;
            while h < 6
              invariant 0 <= h <= 6
            {
              if h != i && h != j {
                var g2 := gcd(h + 1, i + 1);
                if g2 == 1 {
                  dp[len, i, j] := (dp[len, i, j] + dp[len - 1, h, i]) % mod;
                }
              }
              h := h + 1;
            }
          }
        }
        j := j + 1;
      }
      i := i + 1;
    }
    len := len + 1;
  }
  
  // Sum all possibilities for length n
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant ans >= 0
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant ans >= 0
    {
      ans := (ans + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := ans;
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires n >= 0
  ensures result >= 1
{
  if n == 0 {
    result := 1;
    return;
  }
  
  var cnt := new int[82]; // Max digit sum for numbers up to 10000 is 9*4 + 1 = 37, but we use 82 for safety
  var i := 0;
  while i < 82
    invariant 0 <= i <= 82
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var ans := 0;
  var mx := 0;
  
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant ans >= 0
    invariant mx >= 0
  {
    var s := digitSum(i);
    if s < 82 {
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
}

method intToString(n: int) returns (s: seq<char>)
  requires n >= 0
  ensures |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if n == 0 {
    s := ['0'];
    return;
  }
  
  var digits := [];
  var num := n;
  while num > 0
    invariant num >= 0
    invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
    invariant num == 0 ==> |digits| >= 1
  {
    var digit := num % 10;
    var digitChar := ('0' as int + digit) as char;
    digits := [digitChar] + digits;
    num := num / 10;
  }
  s := digits;
}

method stringToInt(s: seq<char>) returns (n: int)
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
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
}

method reverseSeq(s: seq<char>) returns (reversed: seq<char>)
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures |reversed| == |s|
  ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
  ensures forall i :: 0 <= i < |s| ==> '0' <= reversed[i] <= '9'
{
  reversed := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |reversed| == |s| - i
    invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == s[|s| - 1 - j]
    invariant forall j :: 0 <= j < |reversed| ==> '0' <= reversed[j] <= '9'
  {
    i := i - 1;
    reversed := reversed + [s[i]];
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n
  ensures result >= -1
{
  if n > 2147483647 {
    result := -1;
    return;
  }
  
  var cs := intToString(n);
  var len := |cs|;
  
  if len <= 1 {
    result := -1;
    return;
  }
  
  var i := len - 2;
  
  // Find the rightmost character that is smaller than its next character
  while i >= 0 && cs[i] >= cs[i + 1]
    invariant -1 <= i < len - 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    result := -1;
    return;
  }
  
  // Find the smallest character on right side of above character that is greater than cs[i]
  var j := len - 1;
  while cs[i] >= cs[j]
    invariant i < j < len
    decreases j
  {
    j := j - 1;
  }
  
  // Swap characters
  var temp := cs[i];
  cs := cs[i := cs[j]];
  cs := cs[j := temp];
  
  // Reverse the suffix starting at cs[i+1]
  var suffix := cs[i + 1..];
  var reversedSuffix := reverseSeq(suffix);
  cs := cs[..i + 1] + reversedSuffix;
  
  var ans := stringToInt(cs);
  
  if ans > 2147483647 {
    result := -1;
  } else {
    result := ans;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures true
{
  var o1 := distinctSequences_2318(o);
  var o2 := countLargestGroup_1399(o1);
  var o3 := nextGreaterElement_556(o2);
  result := o3;
}
