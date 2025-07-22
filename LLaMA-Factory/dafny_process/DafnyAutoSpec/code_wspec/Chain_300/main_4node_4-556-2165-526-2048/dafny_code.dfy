
method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures -1 <= result <= 2147483647
{
  var digits := intToDigits(n);
  var len := |digits|;
  
  if len <= 1 {
    return -1;
  }
  
  var i := len - 2;
  
  // Find the rightmost digit that is smaller than the digit next to it
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
  
  // Find the smallest digit on right side of above character that is greater than digits[i]
  while digits[i] >= digits[j]
    invariant i < j < len
    decreases j - i
  {
    j := j - 1;
  }
  
  // Swap digits[i] and digits[j]
  var temp := digits[i];
  digits := digits[i := digits[j]][j := temp];
  
  // Reverse the digits after position i
  digits := digits[..i+1] + reverse(digits[i+1..]);
  
  // Ensure digits still satisfy the precondition for digitsToInt
  assert forall k :: 0 <= k < |digits| ==> 0 <= digits[k] <= 9;
  
  var ans := digitsToInt(digits);
  if ans > 2147483647 {
    return -1;
  } else {
    assert ans <= 2147483647;
    return ans;
  }
}

method smallestNumber_2165(num: int) returns (result: int)
  requires -1000000000000000 <= num <= 1000000000000000
  ensures result >= -9876543210 && result <= 9876543210
  ensures result != 0
{
  var neg := num < 0;
  var absNum := if num < 0 then -num else num;
  
  var cnt := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant forall k :: 0 <= k < i ==> cnt[k] == 0
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var temp := absNum;
  while temp > 0
    invariant temp >= 0
    invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
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
      invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
      invariant ans >= 0
      decreases i + 1
    {
      var j := 0;
      while j < cnt[i]
        invariant 0 <= j <= cnt[i]
        invariant cnt[i] >= 0
        invariant ans >= 0
        decreases cnt[i] - j
      {
        if ans <= 987654321 {
          ans := ans * 10 + i;
        }
        j := j + 1;
      }
      i := i - 1;
    }
    if ans == 0 {
      return -1;
    }
    if ans > 9876543210 {
      return -9876543210;
    }
    return -ans;
  } else {
    // Handle leading zero case
    if cnt[0] > 0 {
      i := 1;
      while i < 10 && cnt[i] == 0
        invariant 1 <= i <= 10
        decreases 10 - i
      {
        i := i + 1;
      }
      if i < 10 {
        ans := i;
        cnt[i] := cnt[i] - 1;
      }
    }
    
    i := 0;
    while i < 10
      invariant 0 <= i <= 10
      invariant forall k :: 0 <= k < 10 ==> cnt[k] >= 0
      invariant ans >= 0
      decreases 10 - i
    {
      var j := 0;
      while j < cnt[i]
        invariant 0 <= j <= cnt[i]
        invariant cnt[i] >= 0
        invariant ans >= 0
        decreases cnt[i] - j
      {
        if ans <= 987654321 {
          ans := ans * 10 + i;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    
    if ans == 0 {
      return 1;
    } else {
      if ans > 9876543210 {
        return 9876543210;
      }
      return ans;
    }
  }
}

method countArrangement_526(n: int) returns (result: int)
  requires 1 <= n <= 15
  ensures 0 <= result <= 1000000
{
  var vis := new bool[n + 1];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
  {
    vis[i] := false;
    i := i + 1;
  }
  
  var count := dfs(1, n, vis);
  return count;
}

method dfs(pos: int, n: int, vis: array<bool>) returns (count: int)
  requires 1 <= pos <= n + 1
  requires 1 <= n <= 15
  requires vis.Length == n + 1
  modifies vis
  ensures count >= 0
  ensures count <= 1000000
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
    invariant count <= 1000000
    decreases n + 1 - j
  {
    if !vis[j] && (j % pos == 0 || pos % j == 0) {
      vis[j] := true;
      var subCount := dfs(pos + 1, n, vis);
      if count + subCount <= 1000000 {
        count := count + subCount;
      } else {
        count := 1000000;
      }
      vis[j] := false;
    }
    j := j + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures result > n
  decreases *
{
  var x := n + 1;
  while true
    invariant x > n
    decreases *
  {
    if isBeautiful(x) {
      return x;
    }
    x := x + 1;
  }
}

predicate isBeautiful(x: int)
  requires x >= 0
{
  var digits := intToDigits(x);
  var cnt := countDigits(digits);
  forall i :: 0 <= i < |cnt| ==> (cnt[i] == 0 || cnt[i] == i)
}

function countDigits(digits: seq<int>): seq<int>
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
{
  var cnt := seq(10, _ => 0);
  countDigitsHelper(digits, cnt, 0)
}

function countDigitsHelper(digits: seq<int>, cnt: seq<int>, index: int): seq<int>
  requires |cnt| == 10
  requires 0 <= index <= |digits|
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  decreases |digits| - index
{
  if index == |digits| then cnt
  else 
    var digit := digits[index];
    var newCnt := cnt[digit := cnt[digit] + 1];
    countDigitsHelper(digits, newCnt, index + 1)
}

function intToDigits(n: int): seq<int>
  requires n >= 0
  ensures |intToDigits(n)| >= 1
  ensures forall i :: 0 <= i < |intToDigits(n)| ==> 0 <= intToDigits(n)[i] <= 9
{
  if n == 0 then [0]
  else intToDigitsHelper(n, [])
}

function intToDigitsHelper(n: int, acc: seq<int>): seq<int>
  requires n > 0
  requires forall i :: 0 <= i < |acc| ==> 0 <= acc[i] <= 9
  ensures |intToDigitsHelper(n, acc)| >= 1
  ensures forall i :: 0 <= i < |intToDigitsHelper(n, acc)| ==> 0 <= intToDigitsHelper(n, acc)[i] <= 9
  decreases n
{
  if n < 10 then [n] + acc
  else intToDigitsHelper(n / 10, [n % 10] + acc)
}

function digitsToInt(digits: seq<int>): int
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures digitsToInt(digits) >= 0
{
  digitsToIntHelper(digits, 0, 0)
}

function digitsToIntHelper(digits: seq<int>, index: int, acc: int): int
  requires 0 <= index <= |digits|
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires acc >= 0
  ensures digitsToIntHelper(digits, index, acc) >= 0
  decreases |digits| - index
{
  if index == |digits| then acc
  else digitsToIntHelper(digits, index + 1, acc * 10 + digits[index])
}

function reverse<T>(s: seq<T>): seq<T>
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 then []
  else reverse(s[1..]) + [s[0]]
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 2147483648
  ensures result >= 0
  decreases *
{
  var o1 := nextGreaterElement_556(o);
  if o1 == -1 {
    // Handle the case where no greater element exists
    // We'll use a default value that works with the next function
    o1 := 1;
  }
  var o2 := smallestNumber_2165(o1);
  // Clamp o2 to valid range for countArrangement_526
  if o2 > 15 {
    o2 := 15;
  } else if o2 < 1 {
    o2 := 1;
  }
  var o3 := countArrangement_526(o2);
  var o4 := nextBeautifulNumber_2048(o3);
  result := o4;
}
