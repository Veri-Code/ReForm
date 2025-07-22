
function gcd_func(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd_func(b, a % b)
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
    invariant gcd_func(a, b) == gcd_func(x, y)
    decreases y
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  result := x;
}

function power10_func(exp: int): int
  requires 0 <= exp <= 10
  ensures power10_func(exp) > 0
{
  if exp == 0 then 1 else 10 * power10_func(exp - 1)
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 15
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
  // Initialize dp array to 0
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
  
  // Fill dp[2]
  var i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      var g := gcd(i + 1, j + 1);
      if g == 1 && i != j {
        dp[2, i, j] := 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Fill dp for k >= 3
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
        var g1 := gcd(i + 1, j + 1);
        if g1 == 1 && i != j {
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
          {
            var g2 := gcd(h + 1, i + 1);
            if g2 == 1 && h != i && h != j {
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
  
  // Sum all dp[n][i][j]
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
    {
      ans := ans + dp[n, i, j];
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := if ans == 0 then 1 else ans % mod;
  if result <= 0 { result := 1; }
  if result > 15 { result := 15; }
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures 1 <= result <= 1000
{
  var ans := 0;
  var vis := new bool[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  // Build match array
  var matchArray := new seq<int>[n + 1];
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    var matches: seq<int> := [];
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant |matches| <= j - 1
    {
      if j % i == 0 || i % j == 0 {
        matches := matches + [j];
      }
      j := j + 1;
    }
    matchArray[i] := matches;
    i := i + 1;
  }
  
  ans := dfs_helper(1, n, vis, matchArray);
  result := if ans == 0 then 1 else ans;
  if result > 1000 { result := 1000; }
}

method dfs_helper(pos: int, n: int, vis: array<bool>, matchArray: array<seq<int>>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires vis.Length == n + 1
  requires matchArray.Length == n + 1
  ensures count >= 0
  modifies vis
  decreases n + 1 - pos
{
  if pos == n + 1 {
    count := 1;
    return;
  }
  
  count := 0;
  var i := 0;
  while i < |matchArray[pos]|
    invariant 0 <= i <= |matchArray[pos]|
    invariant count >= 0
  {
    var j := matchArray[pos][i];
    if 1 <= j <= n && !vis[j] {
      vis[j] := true;
      var subcount := dfs_helper(pos + 1, n, vis, matchArray);
      count := count + subcount;
      vis[j] := false;
    }
    i := i + 1;
  }
}

method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures 1 <= result <= 1000000000
{
  var sum := 0;
  var x := 1;
  while x <= n
    invariant 1 <= x <= n + 1
    invariant sum >= 0
  {
    if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
      sum := sum + x;
    }
    x := x + 1;
  }
  result := if sum == 0 then 1 else sum;
  if result > 1000000000 { result := 1000000000; }
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures -1000000000000000 <= result <= 1000000000000000
  decreases 1000000000 - n + 1
{
  var a := 0; // odd digits
  var b := 0; // even digits
  var k := 0; // total digits
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
    var x := power10(if k <= 15 then k else 15);
    var y := if k / 2 > 0 then power10_func(if k / 2 <= 10 then k / 2 else 10) - 1 else 0;
    result := x + y;
  } else if a == b {
    result := n;
  } else {
    if n < 1000000000 {
      result := closestFair_2417(n + 1);
    } else {
      result := 1000000000000000; // fallback for large values
    }
  }
  
  if result < -1000000000000000 { result := -1000000000000000; }
  if result > 1000000000000000 { result := 1000000000000000; }
}

method power10(exp: int) returns (result: int)
  requires 0 <= exp <= 15
  ensures result > 0
{
  if exp > 10 {
    result := 100000000000; // 10^11 as fallback
    return;
  }
  result := 1;
  var i := 0;
  while i < exp
    invariant 0 <= i <= exp
    invariant result > 0
    invariant result == power10_func(i)
  {
    result := result * 10;
    i := i + 1;
  }
}

method abs(x: int) returns (result: int)
  ensures result >= 0
  ensures result == x || result == -x
{
  if x >= 0 {
    result := x;
  } else {
    result := -x;
  }
}

method smallestNumber_2165(num: int) returns (result: int)
  requires -1000000000000000 <= num <= 1000000000000000
  ensures -1000000000000000 <= result <= 1000000000000000
{
  var neg := num < 0;
  var absNum := abs(num);
  var cnt := new int[10];
  
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var temp := absNum;
  while temp > 0
    invariant temp >= 0
    decreases temp
  {
    var digit := temp % 10;
    cnt[digit] := cnt[digit] + 1;
    temp := temp / 10;
  }
  
  var ans := 0;
  if neg {
    i := 9;
    while i >= 0
      invariant -1 <= i <= 9
    {
      if cnt[i] > 0 {
        var j := 0;
        while j < cnt[i]
          invariant 0 <= j <= cnt[i]
        {
          ans := ans * 10 + i;
          j := j + 1;
        }
      }
      i := i - 1;
    }
    result := -ans;
  } else {
    if cnt[0] > 0 {
      i := 1;
      while i < 10
        invariant 1 <= i <= 10
      {
        if cnt[i] > 0 {
          ans := i;
          cnt[i] := cnt[i] - 1;
          break;
        }
        i := i + 1;
      }
    }
    
    i := 0;
    while i < 10
      invariant 0 <= i <= 10
    {
      if cnt[i] > 0 {
        var j := 0;
        while j < cnt[i]
          invariant 0 <= j <= cnt[i]
        {
          ans := ans * 10 + i;
          j := j + 1;
        }
      }
      i := i + 1;
    }
    result := ans;
  }
  
  // Ensure result is within bounds
  if result < -1000000000000000 {
    result := -1000000000000000;
  } else if result > 1000000000000000 {
    result := 1000000000000000;
  }
}

method main_5node_8(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures -1000000000000000 <= result <= 1000000000000000
{
  var o1 := distinctSequences_2318(o);
  var o2 := countArrangement_526(o1);
  var o3 := sumOfMultiples_2652(o2);
  var o4 := closestFair_2417(o3);
  var o5 := smallestNumber_2165(o4);
  result := o5;
}
