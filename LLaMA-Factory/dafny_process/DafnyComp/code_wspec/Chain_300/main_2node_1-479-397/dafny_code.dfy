
method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 1336
{
  var mx := power10(n) - 1;
  var a := mx;
  
  while a > mx / 10
    invariant mx / 10 <= a <= mx
    invariant mx == power10(n) - 1
    decreases a
  {
    // Create palindrome by mirroring a
    var b := a;
    var x := a;
    
    while b > 0
      invariant b >= 0
      invariant x >= a
      decreases b
    {
      x := x * 10 + b % 10;
      b := b / 10;
    }
    
    // Check if x can be expressed as product of two n-digit numbers
    var t := mx;
    while t * t >= x && t > mx / 10
      invariant t >= mx / 10
      invariant t <= mx
      decreases t
    {
      if x % t == 0 {
        var quotient := x / t;
        if quotient <= mx && quotient > mx / 10 {
          assert x % 1337 >= 0;
          assert x % 1337 < 1337;
          if x % 1337 == 0 {
            return 1336;
          } else {
            return x % 1337;
          }
        }
      }
      t := t - 1;
    }
    
    a := a - 1;
  }
  
  return 9;
}

function integerReplacementSteps(n: int): int
  requires n >= 1
  decreases if n == 1 then 0 else if n % 2 == 0 then n else if n % 4 == 1 || n == 3 then n else n + 2
{
  if n == 1 then 0
  else if n % 2 == 0 then 1 + integerReplacementSteps(n / 2)
  else if n == 3 || n % 4 == 1 then 1 + integerReplacementSteps(n - 1)
  else 1 + integerReplacementSteps(n + 1)
}

lemma integerReplacementStepsNonNegative(n: int)
  requires n >= 1
  ensures integerReplacementSteps(n) >= 0
  decreases if n == 1 then 0 else if n % 2 == 0 then n else if n % 4 == 1 || n == 3 then n else n + 2
{
  if n == 1 {
    // Base case: integerReplacementSteps(1) == 0 >= 0
  } else if n % 2 == 0 {
    integerReplacementStepsNonNegative(n / 2);
  } else if n == 3 || n % 4 == 1 {
    integerReplacementStepsNonNegative(n - 1);
  } else {
    integerReplacementStepsNonNegative(n + 1);
  }
}

method integerReplacement_397(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures result >= 0
  ensures result == integerReplacementSteps(n)
{
  integerReplacementStepsNonNegative(n);
  
  var current := n;
  var ans := 0;
  
  while current != 1
    invariant current >= 1
    invariant ans >= 0
    invariant ans + integerReplacementSteps(current) == integerReplacementSteps(n)
    decreases if current == 1 then 0 else if current % 2 == 0 then current else if current % 4 == 1 || current == 3 then current else current + 2
  {
    if current % 2 == 0 {
      current := current / 2;
    } else if current != 3 && current % 4 == 3 {
      current := current + 1;
    } else {
      current := current - 1;
    }
    ans := ans + 1;
  }
  
  return ans;
}

function power10(n: int): int
  requires 0 <= n <= 8
  ensures power10(n) >= 1
{
  if n == 0 then 1
  else if n == 1 then 10
  else if n == 2 then 100
  else if n == 3 then 1000
  else if n == 4 then 10000
  else if n == 5 then 100000
  else if n == 6 then 1000000
  else if n == 7 then 10000000
  else 100000000
}

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 8
  ensures result >= 0
{
  var o1 := largestPalindrome_479(o);
  var o2 := integerReplacement_397(o1);
  return o2;
}
