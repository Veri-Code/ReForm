
method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures 1 <= result <= 100000
  decreases *
{
  var current := n;
  
  while true
    invariant 2 <= current <= 100000
    decreases *
  {
    var t := current;
    var s := 0;
    var i := 2;
    var temp := current;
    
    // Factor current and sum the prime factors
    while i <= temp / i
      invariant 2 <= i
      invariant s >= 0
      invariant temp >= 1
      invariant current >= 1
    {
      while temp % i == 0
        invariant temp >= 1
        invariant i >= 2
        invariant s >= 0
        invariant current >= 1
        decreases temp
      {
        temp := temp / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    if temp > 1 {
      s := s + temp;
    }
    
    if s == t {
      return t;
    }
    
    if s >= 2 && s <= 100000 {
      current := s;
    } else {
      return t;
    }
  }
}

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 1 <= result <= 15
{
  var mod := 1000000007;
  var f := new int[n + 1];
  
  // Initialize array
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
  {
    f[k] := 0;
    k := k + 1;
  }
  f[0] := 1;
  
  // Process coin 1
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant f[0] == 1
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  // Process coin 2
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
  {
    f[j] := (f[j] + f[j - 2]) % mod;
    j := j + 1;
  }
  
  // Process coin 6
  if n >= 6 {
    j := 6;
    while j <= n
      invariant 6 <= j <= n + 1
    {
      f[j] := (f[j] + f[j - 6]) % mod;
      j := j + 1;
    }
  }
  
  var ans := f[n];
  if n >= 4 {
    ans := (ans + f[n - 4]) % mod;
  }
  if n >= 8 {
    ans := (ans + f[n - 8]) % mod;
  }
  
  // Return a value in the required range
  result := (ans % 15) + 1;
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures 1 <= result <= 1000
{
  // Create match array - for each position i, store which numbers can go there
  var matchArray := new seq<int>[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    matchArray[i] := [];
    i := i + 1;
  }
  
  // Fill match array
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
    {
      if j % i == 0 || i % j == 0 {
        matchArray[i] := matchArray[i] + [j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  var vis := new bool[n + 1];
  i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  var count := dfs_helper(1, n, matchArray, vis);
  result := if count == 0 then 1 else if count > 1000 then 1000 else count;
}

method dfs_helper(pos: int, n: int, matchArray: array<seq<int>>, vis: array<bool>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires matchArray.Length == n + 1
  requires vis.Length == n + 1
  ensures count >= 0
  modifies vis
  decreases n + 1 - pos
{
  if pos == n + 1 {
    return 1;
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
      var subcount := dfs_helper(pos + 1, n, matchArray, vis);
      count := count + subcount;
      vis[j] := false;
    }
    i := i + 1;
  }
}

method sumOfMultiples_2652(n: int) returns (result: int)
  requires 1 <= n <= 1000
  ensures 1 <= result <= 8
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
  
  // Return a value in the required range
  result := (sum % 8) + 1;
}

method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures result >= 0
{
  if n == 1 {
    return 9;
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
    decreases a
  {
    // Create palindrome
    var b := a;
    var x := a;
    while b > 0
      invariant b >= 0
      invariant x >= 0
      decreases b
    {
      x := x * 10 + b % 10;
      b := b / 10;
    }
    
    // Check if x can be expressed as product of two n-digit numbers
    var t := mx;
    while t * t >= x && t > mx / 10
      invariant t >= 0
      decreases t
    {
      if x % t == 0 && x / t <= mx {
        return x % 1337;
      }
      t := t - 1;
    }
    a := a - 1;
  }
  
  return 9;
}

method main_5node_8(o: int) returns (result: int)
  requires 2 <= o <= 100000
  ensures result >= 0
  decreases *
{
  var o1 := smallestValue_2507(o);
  var o2 := numberOfWays_3183(o1);
  var o3 := countArrangement_526(o2);
  var o4 := sumOfMultiples_2652(o3);
  var o5 := largestPalindrome_479(o4);
  result := o5;
}
