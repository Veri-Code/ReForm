
method DigitCount(n: int) returns (counts: array<int>)
  requires n >= 0
  ensures counts.Length == 10
  ensures forall i :: 0 <= i < 10 ==> counts[i] >= 0
{
  counts := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant forall j :: 0 <= j < i ==> counts[j] == 0
  {
    counts[i] := 0;
    i := i + 1;
  }
  
  var y := n;
  while y > 0
    invariant y >= 0
    invariant forall i :: 0 <= i < 10 ==> counts[i] >= 0
  {
    var digit := y % 10;
    counts[digit] := counts[digit] + 1;
    y := y / 10;
  }
}

function IsBeautiful(n: int): bool
  requires n >= 0
{
  var counts := DigitCountSeq(n);
  forall i :: 0 <= i < 10 ==> (counts[i] == 0 || counts[i] == i)
}

function DigitCountSeq(n: int): seq<int>
  requires n >= 0
  ensures |DigitCountSeq(n)| == 10
  ensures forall i :: 0 <= i < 10 ==> DigitCountSeq(n)[i] >= 0
{
  var counts := seq(10, i => 0);
  DigitCountHelper(n, counts)
}

function DigitCountHelper(n: int, counts: seq<int>): seq<int>
  requires n >= 0
  requires |counts| == 10
  requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
  ensures |DigitCountHelper(n, counts)| == 10
  ensures forall i :: 0 <= i < 10 ==> DigitCountHelper(n, counts)[i] >= 0
{
  if n == 0 then counts
  else
    var digit := n % 10;
    var newCounts := counts[digit := counts[digit] + 1];
    DigitCountHelper(n / 10, newCounts)
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures result > n
  ensures result >= 0
  ensures result <= 1000000000
{
  var x := n + 1;
  while x <= 1000000000
    invariant x > n
    invariant x >= 1
  {
    var counts := DigitCount(x);
    var beautiful := true;
    var i := 0;
    while i < 10 && beautiful
      invariant 0 <= i <= 10
      invariant beautiful ==> forall j :: 0 <= j < i ==> (counts[j] == 0 || counts[j] == j)
    {
      if counts[i] != 0 && counts[i] != i {
        beautiful := false;
      }
      i := i + 1;
    }
    
    if beautiful {
      result := x;
      return;
    }
    x := x + 1;
  }
  
  // This should not be reached given the problem constraints
  // But we need to satisfy the postcondition
  result := 1000000000;
}

method IntToDigits(n: int) returns (digits: seq<int>)
  requires n >= 0
  ensures |digits| >= 1
  ensures forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  if n == 0 {
    digits := [0];
    return;
  }
  
  digits := [];
  var temp := n;
  while temp > 0
    invariant temp >= 0
    invariant forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    invariant temp == 0 ==> |digits| >= 1
  {
    var digit := temp % 10;
    digits := [digit] + digits;
    temp := temp / 10;
  }
}

method DigitsToInt(digits: seq<int>) returns (result: int)
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures result >= 0
{
  result := 0;
  var i := 0;
  while i < |digits|
    invariant 0 <= i <= |digits|
    invariant result >= 0
  {
    result := result * 10 + digits[i];
    i := i + 1;
  }
}

method monotoneIncreasingDigits_738(n: int) returns (result: int)
  requires 0 <= n <= 1000000000
  ensures 0 <= result <= n
{
  if n == 0 {
    result := 0;
    return;
  }
  
  var digits := IntToDigits(n);
  var s := digits;
  
  var i := 1;
  while i < |s| && s[i-1] <= s[i]
    invariant 1 <= i <= |s|
    invariant forall j :: 1 <= j < i ==> s[j-1] <= s[j]
  {
    i := i + 1;
  }
  
  if i < |s| {
    while i > 0 && i < |s| && s[i-1] > s[i]
      invariant 0 <= i < |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    {
      if s[i-1] > 0 {
        s := s[i-1 := s[i-1] - 1];
      }
      i := i - 1;
    }
    
    i := i + 1;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |s| ==> 0 <= s[j] <= 9
    {
      s := s[i := 9];
      i := i + 1;
    }
  }
  
  var temp_result := DigitsToInt(s);
  if temp_result <= n {
    result := temp_result;
  } else {
    result := n;
  }
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures result >= 0
{
  var vis := new bool[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  result := dfs(1, n, vis);
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires vis.Length == n + 1
  ensures count >= 0
  modifies vis
  decreases n + 1 - pos
{
  if pos == n + 1 {
    count := 1;
    return;
  }
  
  count := 0;
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant count >= 0
  {
    if !vis[j] && (j % pos == 0 || pos % j == 0) {
      vis[j] := true;
      var subCount := dfs(pos + 1, n, vis);
      count := count + subCount;
      vis[j] := false;
    }
    j := j + 1;
  }
}

method main_3node_2(o: int) returns (result: int)
  requires 0 <= o <= 1000000
  ensures result >= 0
{
  var o1 := nextBeautifulNumber_2048(o);
  if o1 <= 15 {
    var o2 := monotoneIncreasingDigits_738(o1);
    if o2 >= 1 {
      var o3 := countArrangement_526(o2);
      result := o3;
    } else {
      result := 0;
    }
  } else {
    result := 0;
  }
}
