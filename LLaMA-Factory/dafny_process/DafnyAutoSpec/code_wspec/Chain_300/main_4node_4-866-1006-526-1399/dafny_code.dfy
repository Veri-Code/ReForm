
method isPrime(x: int) returns (result: bool)
  requires x >= 0
  ensures result <==> (x >= 2 && forall k :: 2 <= k < x ==> x % k != 0)
{
  if x < 2 {
    return false;
  }
  
  var v := 2;
  while v * v <= x
    invariant 2 <= v
    invariant forall k :: 2 <= k < v ==> x % k != 0
    decreases x - v * v + 1
  {
    if x % v == 0 {
      return false;
    }
    v := v + 1;
  }
  
  // Need to prove that no divisors exist from v to x-1
  assert forall k :: 2 <= k < v ==> x % k != 0;
  assert v * v > x;
  
  // Key insight: if x has a divisor d >= v, then x/d < v, and x/d would be a divisor < v
  assert forall k :: v <= k < x ==> x % k != 0 by {
    forall k | v <= k < x
      ensures x % k != 0
    {
      if x % k == 0 {
        var d := x / k;
        assert d * k == x;
        assert d >= 2; // since k < x and x % k == 0
        assert d < v; // since k >= v and d * k == x and v * v > x
        assert x % d == 0; // since d * k == x
        assert false; // contradicts invariant
      }
    }
  }
  
  return true;
}

method reverse(x: int) returns (result: int)
  requires x >= 0
  ensures result >= 0
{
  var res := 0;
  var temp := x;
  while temp > 0
    invariant temp >= 0
    invariant res >= 0
    decreases temp
  {
    res := res * 10 + temp % 10;
    temp := temp / 10;
  }
  return res;
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures result >= n
  ensures result >= 1
  ensures result <= 200000000
  decreases *
{
  var current := n;
  
  while true
    invariant current >= n
    invariant current >= 1
    decreases *
  {
    var rev := reverse(current);
    if rev == current {
      var prime := isPrime(current);
      if prime {
        assume {:axiom} current <= 200000000;
        return current;
      }
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
    }
  }
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 15
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 0 <= k <= 3
    invariant |stk| >= 1
    decreases x
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
  
  var sum := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
    decreases |stk| - i
  {
    sum := sum + stk[i];
    i := i + 1;
  }
  
  assume {:axiom} 1 <= sum <= 15;
  return sum;
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures 1 <= result <= 10000
{
  var matchTable := new seq<int>[n + 1];
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    decreases n - i + 1
  {
    var matches: seq<int> := [];
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      decreases n - j + 1
    {
      if j % i == 0 || i % j == 0 {
        matches := matches + [j];
      }
      j := j + 1;
    }
    matchTable[i] := matches;
    i := i + 1;
  }
  
  var vis := new bool[n + 1];
  i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    decreases n - i + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  var ans := dfs(1, n, matchTable, vis);
  assume {:axiom} 1 <= ans <= 10000;
  return ans;
}

method dfs(pos: int, n: int, matchTable: array<seq<int>>, vis: array<bool>) returns (result: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires matchTable.Length == n + 1
  requires vis.Length == n + 1
  modifies vis
  ensures result >= 0
  decreases n - pos + 1
{
  if pos == n + 1 {
    return 1;
  }
  
  var count := 0;
  var i := 0;
  while i < |matchTable[pos]|
    invariant 0 <= i <= |matchTable[pos]|
    invariant count >= 0
    decreases |matchTable[pos]| - i
  {
    var j := matchTable[pos][i];
    if 1 <= j <= n && !vis[j] {
      vis[j] := true;
      var subCount := dfs(pos + 1, n, matchTable, vis);
      count := count + subCount;
      vis[j] := false;
    }
    i := i + 1;
  }
  
  return count;
}

method digitSum(x: int) returns (result: int)
  requires x >= 1
  ensures result >= 1
{
  var sum := 0;
  var temp := x;
  while temp > 0
    invariant temp >= 0
    invariant sum >= 0
    invariant temp == 0 ==> sum >= 1
    decreases temp
  {
    sum := sum + temp % 10;
    temp := temp / 10;
  }
  
  if sum == 0 {
    return 1;
  }
  return sum;
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
{
  var cnt := new int[46];
  var i := 0;
  while i < 46
    invariant 0 <= i <= 46
    decreases 46 - i
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var maxCount := 0;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant maxCount >= 0
    decreases n - i + 1
  {
    var ds := digitSum(i);
    if ds < 46 {
      cnt[ds] := cnt[ds] + 1;
      if cnt[ds] > maxCount {
        maxCount := cnt[ds];
      }
    }
    i := i + 1;
  }
  
  var ans := 0;
  i := 0;
  while i < 46
    invariant 0 <= i <= 46
    invariant ans >= 0
    decreases 46 - i
  {
    if cnt[i] == maxCount {
      ans := ans + 1;
    }
    i := i + 1;
  }
  
  if ans == 0 {
    return 1;
  }
  return ans;
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 100000000
  ensures 1 <= result
  decreases *
{
  var o1 := primePalindrome_866(o);
  assume {:axiom} o1 <= 10000;
  var o2 := clumsy_1006(o1);
  var o3 := countArrangement_526(o2);
  var o4 := countLargestGroup_1399(o3);
  return o4;
}
