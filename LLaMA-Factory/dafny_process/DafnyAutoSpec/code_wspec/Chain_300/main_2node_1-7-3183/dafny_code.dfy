
method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= result <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp_x := x;
  
  while temp_x != 0
    invariant mi == -2147483648
    invariant mx == 2147483647
    invariant -2147483648 <= ans <= 2147483647
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
    // Check for overflow before multiplying by 10
    if ans < mi / 10 + 1 || ans > mx / 10 {
      result := 0;
      return;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    // Update ans and temp_x
    var new_ans := ans * 10 + y;
    if new_ans < -2147483648 || new_ans > 2147483647 {
      result := 0;
      return;
    }
    
    ans := new_ans;
    temp_x := (temp_x - y) / 10;
  }
  
  if ans < 0 {
    result := 0;
  } else {
    result := ans;
  }
}

method numberOfWays_3183(n: int) returns (result: int)
  requires 1 <= n <= 100000
  ensures 0 <= result < 1000000007
{
  var mod := 1000000007;
  var f := new int[n + 1];
  
  // Initialize array
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> f[k] == 0
  {
    f[i] := 0;
    i := i + 1;
  }
  f[0] := 1;
  
  // Process coin 1
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant f[0] == 1
    invariant forall k :: 1 <= k < j ==> 0 <= f[k] < mod
    invariant forall k :: j <= k <= n ==> f[k] == 0
  {
    f[j] := (f[j] + f[j - 1]) % mod;
    j := j + 1;
  }
  
  // Process coin 2
  j := 2;
  while j <= n
    invariant 2 <= j <= n + 1
    invariant f[0] == 1
    invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
  {
    f[j] := (f[j] + f[j - 2]) % mod;
    j := j + 1;
  }
  
  // Process coin 6
  if n >= 6 {
    j := 6;
    while j <= n
      invariant 6 <= j <= n + 1
      invariant f[0] == 1
      invariant forall k :: 0 <= k <= n ==> 0 <= f[k] < mod
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
  
  result := ans;
}

method main_2node_1(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures true
{
  var o1 := reverse_7(o);
  if o1 == 0 {
    result := 0;
    return;
  }
  if o1 < 1 || o1 > 100000 {
    result := 0;
    return;
  }
  var o2 := numberOfWays_3183(o1);
  result := o2;
}
