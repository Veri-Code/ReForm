
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
{
  if n == 1 {
    return 6;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize all entries to 0
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
  {
    var i := 0;
    while i < 6
      invariant 0 <= i <= 6
    {
      var j := 0;
      while j < 6
        invariant 0 <= j <= 6
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
  
  // Fill DP table for lengths 3 to n
  k := 3;
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
  
  // Sum all valid sequences of length n
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
  
  if ans == 0 {
    result := 1;
  } else {
    result := ans;
  }
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires 1 <= n
  ensures result >= 1
{
  var cnt := new int[100]; // digit sums can be at most 9*4 = 36 for n <= 10000
  var i := 0;
  while i < 100
    invariant 0 <= i <= 100
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
    var temp := i;
    var s := 0;
    while temp > 0
      invariant temp >= 0
      invariant s >= 0
      decreases temp
    {
      s := s + (temp % 10);
      temp := temp / 10;
    }
    
    if s < 100 {
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
  
  if ans == 0 {
    result := 1;
  } else {
    result := ans;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n
  ensures true
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant a1 >= 1
    decreases cnt
  {
    if i % 2 == 1 {
      an := an - step;
      if cnt % 2 == 1 {
        a1 := a1 + step;
      }
    } else {
      a1 := a1 + step;
      if cnt % 2 == 1 {
        an := an - step;
      }
    }
    cnt := cnt / 2;
    step := step * 2;
    i := i + 1;
  }
  
  result := a1;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures true
{
  var o1 := distinctSequences_2318(o);
  var o2 := countLargestGroup_1399(o1);
  var o3 := lastRemaining_390(o2);
  result := o3;
}
