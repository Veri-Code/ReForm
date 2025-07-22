
method largestPalindrome_479(n: int) returns (result: int)
  requires 1 <= n <= 8
  ensures 1 <= result <= 10000
{
  var mx := power10(n) - 1;
  var a := mx;
  
  while a > mx / 10
    invariant mx / 10 <= a <= mx
    invariant mx == power10(n) - 1
    decreases a
  {
    var b := a;
    var x := a;
    
    // Create palindrome by reversing a and appending
    while b > 0
      invariant b >= 0
      invariant x >= a
      decreases b
    {
      x := x * 10 + b % 10;
      b := b / 10;
    }
    
    var t := mx;
    while t * t >= x && t > 0
      invariant t >= 0
      decreases t
    {
      if x % t == 0 {
        var res := x % 1337;
        if res == 0 {
          return 1337;
        }
        return res;
      }
      t := t - 1;
    }
    
    a := a - 1;
  }
  
  return 9;
}

method countLargestGroup_1399(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 1000000000
{
  var cnt := new int[46]; // Max digit sum for numbers up to 10000 is 9*4 = 36, but we use 46 for safety
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
    invariant ans <= i
  {
    var num := i;
    var s := 0;
    
    // Calculate digit sum
    while num > 0
      invariant num >= 0
      invariant s >= 0
      decreases num
    {
      s := s + num % 10;
      num := num / 10;
    }
    
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
  
  return ans;
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
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
    invariant cnt <= n
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
  
  return a1;
}

function power10(n: int): int
  requires 0 <= n <= 8
  ensures power10(n) >= 1
{
  if n == 0 then 1
  else if n == 1 then 10
  else if n == 2 then 100
  else if n == 3 then 1000
  else if n == 4 then 10000
  else if n == 5 then 100000
  else if n == 6 then 1000000
  else if n == 7 then 10000000
  else 100000000
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 8
  ensures true
{
  var o1 := largestPalindrome_479(o);
  var o2 := countLargestGroup_1399(o1);
  var o3 := lastRemaining_390(o2);
  result := o3;
}
