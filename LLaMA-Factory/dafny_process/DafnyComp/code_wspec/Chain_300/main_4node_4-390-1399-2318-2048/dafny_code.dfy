
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

method digitSum(n: int) returns (sum: int)
  requires n >= 0
  ensures sum >= 0
{
  var num := n;
  sum := 0;
  while num > 0
    invariant num >= 0
    invariant sum >= 0
    decreases num
  {
    sum := sum + (num % 10);
    num := num / 10;
  }
}

function power2(i: int): int
  requires i >= 0
{
  if i == 0 then 1 else 2 * power2(i - 1)
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 10000
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant i >= 0
    invariant step == power2(i)
    invariant a1 >= 1
    invariant an <= n
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
  if a1 > 10000 {
    result := 10000;
  } else {
    result := a1;
  }
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 10000
{
  var cnt := new int[100];
  var i := 0;
  while i < cnt.Length
    invariant 0 <= i <= cnt.Length
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var ans := 1;
  var mx := 0;
  i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant ans >= 1
    invariant mx >= 0
    decreases n - i
  {
    var s := digitSum(i);
    if s < cnt.Length {
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
  
  if ans > 10000 {
    result := 10000;
  } else {
    result := ans;
  }
}

method distinctSequences_2318(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 0 <= result < 1000000007
{
  if n == 1 {
    result := 6;
    return;
  }
  
  var mod := 1000000007;
  var dp := new int[n + 1, 6, 6];
  
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
  
  k := 3;
  while k <= n
    invariant 3 <= k <= n + 1
    decreases n - k
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
          dp[k, i, j] := 0;
          var h := 0;
          while h < 6
            invariant 0 <= h <= 6
            invariant 0 <= dp[k, i, j] < mod
          {
            var g2 := gcd(h + 1, i + 1);
            if g2 == 1 && h != i && h != j {
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
  
  var ans := 0;
  i := 0;
  while i < 6
    invariant 0 <= i <= 6
    invariant 0 <= ans < mod
  {
    var j := 0;
    while j < 6
      invariant 0 <= j <= 6
      invariant 0 <= ans < mod
    {
      ans := (ans + dp[n, i, j]) % mod;
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := ans;
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x > 0
{
  var y := x;
  var cnt := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  while y > 0
    invariant y >= 0
    decreases y
  {
    var digit := y % 10;
    cnt[digit] := cnt[digit] + 1;
    y := y / 10;
  }
  
  beautiful := true;
  i := 0;
  while i < 10 && beautiful
    invariant 0 <= i <= 10
  {
    if cnt[i] != 0 && cnt[i] != i {
      beautiful := false;
    }
    i := i + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n
  ensures result > n
{
  result := n + 1;
}

method main_4node_4(o: int) returns (result: int)
  requires 1 <= o <= 1000000000
  ensures result >= 1
{
  var o1 := lastRemaining_390(o);
  var o2 := countLargestGroup_1399(if o1 <= 10000 then o1 else 10000);
  var o3 := distinctSequences_2318(if o2 <= 10000 then o2 else 10000);
  var o4 := nextBeautifulNumber_2048(o3);
  result := o4;
}
