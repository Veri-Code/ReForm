
method countTriples_1925(n: int) returns (ans: int)
  requires 1 <= n <= 250
  ensures ans >= 0
{
  ans := 0;
  var a := 1;
  while a < n
    invariant 1 <= a <= n
    invariant ans >= 0
  {
    var b := 1;
    while b < n
      invariant 1 <= b <= n
      invariant ans >= 0
    {
      var x := a * a + b * b;
      var c := isqrt(x);
      if c <= n && c * c == x {
        ans := ans + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }
}

function isqrt(x: int): int
  requires x >= 0
  ensures isqrt(x) >= 0
  ensures isqrt(x) * isqrt(x) <= x
  ensures (isqrt(x) + 1) * (isqrt(x) + 1) > x
{
  if x == 0 then 0
  else if x == 1 then 1
  else
    var guess := x / 2;
    isqrt_helper(x, guess)
}

function isqrt_helper(x: int, guess: int): int
  requires x >= 0
  requires guess > 0
  ensures isqrt_helper(x, guess) >= 0
  ensures isqrt_helper(x, guess) * isqrt_helper(x, guess) <= x
  ensures (isqrt_helper(x, guess) + 1) * (isqrt_helper(x, guess) + 1) > x
  decreases if guess * guess > x then guess else x - guess * guess
{
  if guess * guess == x then guess
  else if guess * guess > x then
    var next := (guess + x / guess) / 2;
    if next <= 0 then 1
    else if next >= guess then guess
    else isqrt_helper(x, next)
  else
    var next := (guess + x / guess) / 2;
    if next <= guess then 
      if guess * guess <= x && (guess + 1) * (guess + 1) > x then guess
      else guess + 1
    else isqrt_helper(x, next)
}

method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures true
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant |stk| >= 1
    invariant k >= 0
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
  
  result := sum_seq(stk);
}

function sum_seq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum_seq(s[1..])
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
    invariant i >= 0
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
  requires 1 <= o <= 250
  ensures true
{
  var o1 := countTriples_1925(o);
  
  if o1 >= 1 && o1 <= 10000 {
    var o2 := clumsy_1006(o1);
    if o2 >= 1 {
      var o3 := lastRemaining_390(o2);
      result := o3;
    } else {
      result := 1;
    }
  } else {
    result := 1;
  }
}
