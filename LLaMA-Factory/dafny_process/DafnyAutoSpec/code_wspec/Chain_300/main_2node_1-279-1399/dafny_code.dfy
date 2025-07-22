
method digitSum(n: int) returns (sum: int)
  requires n >= 1
  ensures sum >= 1
{
  var temp := n;
  sum := 0;
  while temp > 0
    invariant temp >= 0
    invariant sum >= 0
    invariant temp == 0 ==> sum >= 1
    decreases temp
  {
    sum := sum + (temp % 10);
    temp := temp / 10;
  }
  if sum == 0 {
    sum := 1;
  }
}

method numSquares_279(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= n
{
  var m := 0;
  // Calculate floor(sqrt(n))
  while (m + 1) * (m + 1) <= n
    invariant m >= 0
    invariant m * m <= n
    decreases n - m * m
  {
    m := m + 1;
  }
  
  // Initialize DP table
  var f := new int[m + 1, n + 1];
  
  // Initialize all entries to n + 1
  var i := 0;
  while i <= m
    invariant 0 <= i <= m + 1
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] == n + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant forall jj :: 0 <= jj < j ==> f[i, jj] == n + 1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> f[ii, jj] == n + 1
    {
      f[i, j] := n + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Set base case
  f[0, 0] := 0;
  
  // Fill DP table
  i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
    invariant f[0, 0] == 0
    invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
    invariant forall ii :: 1 <= ii < i ==> forall jj :: 0 <= jj <= n ==> f[ii, jj] <= jj + 1
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n + 1
      invariant forall jj :: 0 <= jj < j ==> 0 <= f[i, jj] <= jj + 1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= n ==> 0 <= f[ii, jj] <= n + 1
      invariant f[0, 0] == 0
      invariant forall jj :: 1 <= jj <= n ==> f[0, jj] == n + 1
      invariant forall ii :: 1 <= ii < i ==> forall jj :: 0 <= jj <= n ==> f[ii, jj] <= jj + 1
    {
      f[i, j] := f[i - 1, j];
      if j >= i * i && f[i, j - i * i] < n + 1 {
        var candidate := f[i, j - i * i] + 1;
        if candidate < f[i, j] {
          f[i, j] := candidate;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := f[m, n];
  if result > n {
    result := n;
  }
  
  // Ensure result is at least 1
  if result == 0 {
    result := 1;
  }
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures result >= 1
{
  var maxDigitSum := 40;
  var cnt := new int[maxDigitSum];
  var i := 0;
  while i < maxDigitSum
    invariant 0 <= i <= maxDigitSum
    invariant forall k :: 0 <= k < i ==> cnt[k] == 0
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
    if s < maxDigitSum {
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

method main_2node_1(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures result >= 0
{
  var o1 := numSquares_279(o);
  var o2 := countLargestGroup_1399(o1);
  result := o2;
}
