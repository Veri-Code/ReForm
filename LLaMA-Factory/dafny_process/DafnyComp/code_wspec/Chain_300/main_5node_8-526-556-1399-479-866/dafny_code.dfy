
method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures result >= 1
{
  var ans := 0;
  var vis := new bool[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant vis.Length == n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  ans := dfs_526(1, n, vis);
  if ans == 0 {
    ans := 1;
  }
  return ans;
}

method dfs_526(pos: int, n: int, vis: array<bool>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires vis.Length == n + 1
  ensures count >= 0
  ensures pos == n + 1 ==> count == 1
  ensures pos <= n ==> count >= 0
  modifies vis
  decreases n + 1 - pos
{
  if pos == n + 1 {
    return 1;
  }
  
  count := 0;
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant count >= 0
  {
    if (j % pos == 0 || pos % j == 0) && !vis[j] {
      vis[j] := true;
      var subCount := dfs_526(pos + 1, n, vis);
      count := count + subCount;
      vis[j] := false;
    }
    j := j + 1;
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n
  ensures result >= -1
{
  var digits := intToDigits(n);
  var len := |digits|;
  
  if len <= 1 {
    return -1;
  }
  
  var i := len - 2;
  while i >= 0 && digits[i] >= digits[i + 1]
    invariant -1 <= i < len - 1
    decreases i + 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    return -1;
  }
  
  var j := len - 1;
  while digits[i] >= digits[j]
    invariant i < j < len
    decreases j - i
  {
    j := j - 1;
  }
  
  // Swap digits[i] and digits[j]
  var temp := digits[i];
  digits := digits[i := digits[j]];
  digits := digits[j := temp];
  
  // Reverse digits[i+1..]
  digits := reverseFromIndex(digits, i + 1);
  
  var ans := digitsToInt(digits);
  if ans > 2147483647 || ans <= n {
    return -1;
  } else {
    return ans;
  }
}

function intToDigits(n: int): seq<int>
  requires n >= 0
  ensures |intToDigits(n)| >= 1
  ensures forall i :: 0 <= i < |intToDigits(n)| ==> 0 <= intToDigits(n)[i] <= 9
{
  if n < 10 then [n]
  else intToDigits(n / 10) + [n % 10]
}

function digitsToInt(digits: seq<int>): int
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  if |digits| == 1 then digits[0]
  else digitsToInt(digits[..|digits|-1]) * 10 + digits[|digits|-1]
}

function reverseFromIndex(s: seq<int>, start: int): seq<int>
  requires 0 <= start <= |s|
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures forall i :: 0 <= i < |reverseFromIndex(s, start)| ==> 0 <= reverseFromIndex(s, start)[i] <= 9
{
  s[..start] + reverse(s[start..])
}

function reverse(s: seq<int>): seq<int>
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  ensures forall i :: 0 <= i < |reverse(s)| ==> 0 <= reverse(s)[i] <= 9
{
  if |s| <= 1 then s
  else reverse(s[1..]) + [s[0]]
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
  var ans := 1;
  
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant mx >= 0
    invariant ans >= 1
    invariant ans <= 8
  {
    var digitSum := getDigitSum(i);
    if digitSum < cnt.Length {
      cnt[digitSum] := cnt[digitSum] + 1;
      if mx < cnt[digitSum] {
        mx := cnt[digitSum];
        ans := 1;
      } else if mx == cnt[digitSum] {
        ans := ans + 1;
        if ans > 8 {
          ans := 8;
        }
      }
    }
    i := i + 1;
  }
  
  return ans;
}

function getDigitSum(n: int): int
  requires n >= 0
  ensures getDigitSum(n) >= 0
{
  if n < 10 then n
  else (n % 10) + getDigitSum(n / 10)
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 1337
{
  if n == 1 {
    return 9;
  }
  
  var mx := power10(n) - 1;
  var a := mx;
  
  while a > mx / 10
    invariant mx / 10 <= a <= mx
    decreases a - mx / 10
  {
    var palindrome := createPalindrome(a);
    var t := mx;
    
    while t * t >= palindrome && t > 0
      invariant t >= 0
      decreases t
    {
      if t > 0 && palindrome % t == 0 {
        var res := palindrome % 1337;
        if res == 0 {
          return 1337;
        } else {
          return res;
        }
      }
      t := t - 1;
    }
    a := a - 1;
  }
  
  return 9;
}

function power10(n: int): int
  requires 0 <= n <= 10
  ensures power10(n) >= 1
{
  if n == 0 then 1
  else 10 * power10(n - 1)
}

function createPalindrome(a: int): int
  requires a >= 0
{
  var reversed := reverseInt(a);
  combineInts(a, reversed)
}

function reverseInt(x: int): int
  requires x >= 0
  ensures reverseInt(x) >= 0
{
  if x < 10 then x
  else reverseInt(x / 10) + (x % 10) * power10Safe(countDigitsSafe(x / 10))
}

function countDigitsSafe(x: int): int
  requires x >= 0
  ensures countDigitsSafe(x) >= 1
  ensures countDigitsSafe(x) <= 10
{
  if x < 10 then 1
  else if countDigitsSafe(x / 10) >= 10 then 10
  else 1 + countDigitsSafe(x / 10)
}

function power10Safe(n: int): int
  requires 0 <= n <= 10
  ensures power10Safe(n) >= 1
  decreases n
{
  if n == 0 then 1
  else if n >= 10 then 10000000000
  else 10 * power10Safe(n - 1)
}

function combineInts(a: int, b: int): int
  requires a >= 0 && b >= 0
{
  a * power10Safe(countDigitsSafe(b)) + b
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n
  ensures result >= n
  ensures result >= 2
{
  if n <= 2 {
    return 2;
  }
  if n <= 3 {
    return 3;
  }
  if n <= 5 {
    return 5;
  }
  if n <= 7 {
    return 7;
  }
  if n <= 11 {
    return 11;
  }
  
  var current := n;
  var iterations := 0;
  
  while iterations < 1000000
    invariant current >= n
    invariant iterations >= 0
    decreases 1000000 - iterations
  {
    if isPalindrome(current) && isPrime(current) {
      return current;
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
    iterations := iterations + 1;
  }
  
  return if n <= 1001 then 1001 else n;
}

predicate isPalindrome(x: int)
  requires x >= 0
{
  x == reverseInt(x)
}

predicate isPrime(x: int)
  requires x >= 0
{
  if x < 2 then false
  else forall k :: 2 <= k < x ==> x % k != 0
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 15
  ensures result >= 2
{
  var o1 := countArrangement_526(o);
  var o2 := nextGreaterElement_556(o1);
  var o3_input := if o2 == -1 then 1 else if o2 > 10000 then 10000 else if o2 < 1 then 1 else o2;
  var o3 := countLargestGroup_1399(o3_input);
  var o4 := largestPalindrome_479(o3);
  var o5 := primePalindrome_866(o4);
  result := o5;
}
