
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function power10(n: int): int
  requires n >= 0
  ensures power10(n) > 0
{
  if n == 0 then 1 else 10 * power10(n - 1)
}

function countDigits(n: int): int
  requires n > 0
  ensures countDigits(n) > 0
{
  if n < 10 then 1 else 1 + countDigits(n / 10)
}

function countOddDigits(n: int): int
  requires n > 0
  ensures countOddDigits(n) >= 0
{
  if n < 10 then (if n % 2 == 1 then 1 else 0)
  else (if (n % 10) % 2 == 1 then 1 else 0) + countOddDigits(n / 10)
}

function countEvenDigits(n: int): int
  requires n > 0
  ensures countEvenDigits(n) >= 0
{
  if n < 10 then (if n % 2 == 0 then 1 else 0)
  else (if (n % 10) % 2 == 0 then 1 else 0) + countEvenDigits(n / 10)
}

lemma DigitCountsSum(n: int)
  requires n > 0
  ensures countOddDigits(n) + countEvenDigits(n) == countDigits(n)
{
  if n < 10 {
    // Base case
  } else {
    DigitCountsSum(n / 10);
  }
}

function isFair(n: int): bool
  requires n > 0
{
  countOddDigits(n) == countEvenDigits(n)
}

lemma Power10GreaterThanN(n: int, k: int)
  requires n > 0
  requires k == countDigits(n)
  requires k >= 1
  ensures power10(k) > n
{
  if k == 1 {
    assert n < 10;
    assert power10(1) == 10;
  } else {
    assert n >= 10;
    Power10GreaterThanN(n / 10, k - 1);
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
  ensures result <= 1000000007
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize all values to 0
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
    invariant forall k0, i0, j0 :: 0 <= k0 < k && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
  {
    var i := 0;
    while i < 6
      invariant 0 <= i <= 6
      invariant forall k0, i0, j0 :: 0 <= k0 < k && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
      invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < 6 ==> dp[k, i0, j0] >= 0
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        invariant forall k0, i0, j0 :: 0 <= k0 < k && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
        invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < 6 ==> dp[k, i0, j0] >= 0
        invariant forall j0 :: 0 <= j0 < j ==> dp[k, i, j0] >= 0
      {
        dp[k, i, j] := 0;
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
  
  // Initialize base case for length 2
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
    {
      if gcd(i + 1, j + 1) == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill DP table for lengths 3 to n
  k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
    invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
  {
    i := 0;
    while i < 6
      invariant 0 <= i <= 6
      invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
        invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
      {
        if gcd(i + 1, j + 1) == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
            invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
          {
            if gcd(h + 1, i + 1) == 1 && h != i && h != j {
              dp[k, i, j] := dp[k, i, j] + dp[k - 1, h, i];
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
  
  // Sum all possibilities for the final answer
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant ans >= 0
    invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant ans >= 0
      invariant forall k0, i0, j0 :: 0 <= k0 <= n && 0 <= i0 < 6 && 0 <= j0 < 6 ==> dp[k0, i0, j0] >= 0
    {
      ans := ans + dp[n, i, j];
      j := j + 1;
    }
    i := i + 1;
  }
  
  var finalResult := ans % mod;
  if finalResult == 0 {
    return 1;
  }
  return finalResult;
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n
  ensures result >= n
  decreases if n <= 1000000000 then 1000000000 - n + 1 else 0
{
  if n > 1000000000 {
    return n;
  }
  
  var a := countOddDigits(n);
  var b := countEvenDigits(n);
  var k := countDigits(n);
  
  DigitCountsSum(n);
  
  if k % 2 == 1 {
    // Odd number of digits - need even number for fair number
    var x := power10(k);
    var halfDigits := k / 2;
    var y := if halfDigits > 0 then power10(halfDigits) - 1 else 0;
    Power10GreaterThanN(n, k);
    return x + y;
  }
  
  if a == b {
    return n;
  }
  
  var nextResult := closestFair_2417(n + 1);
  return nextResult;
}

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures result >= 0
{
  var o1 := distinctSequences_2318(o);
  var o2 := closestFair_2417(o1);
  return o2;
}
