
method clumsy_1006(n: int) returns (result: int)
  requires 1 <= n <= 10000
  ensures 1 <= result <= 100000000
{
  var k := 0;
  var stk := [n];
  var x := n - 1;
  
  while x > 0
    invariant 0 <= x <= n - 1
    invariant 0 <= k <= 3
    invariant |stk| >= 1
    invariant forall i :: 0 <= i < |stk| ==> -100000000 <= stk[i] <= 100000000
    decreases x
  {
    var top := stk[|stk| - 1];
    stk := stk[..|stk| - 1];
    
    if k == 0 {
      var product := top * x;
      if product > 100000000 {
        product := 100000000;
      } else if product < -100000000 {
        product := -100000000;
      }
      stk := stk + [product];
    } else if k == 1 {
      var quotient := top / x;
      stk := stk + [quotient];
    } else if k == 2 {
      stk := stk + [x];
    } else {
      stk := stk + [-x];
    }
    
    k := (k + 1) % 4;
    x := x - 1;
  }
  
  result := 0;
  var i := 0;
  while i < |stk|
    invariant 0 <= i <= |stk|
    invariant -100000000 <= result <= 100000000
    decreases |stk| - i
  {
    var new_result := result + stk[i];
    if new_result > 100000000 {
      new_result := 100000000;
    } else if new_result < -100000000 {
      new_result := -100000000;
    }
    result := new_result;
    i := i + 1;
  }
  
  if result < 1 {
    result := 1;
  } else if result > 100000000 {
    result := 100000000;
  }
}

function is_prime(x: int): bool
  requires x >= 0
{
  if x < 2 then false
  else x == 2 || (x % 2 != 0 && forall v :: 3 <= v < x && v * v <= x && v % 2 != 0 ==> x % v != 0)
}

function reverse_digits(x: int): int
  requires x >= 0
  decreases x
{
  if x == 0 then 0
  else if x < 10 then x
  else 
    var div_result := x / 10;
    assert div_result >= 0;
    count_digits_nonneg(div_result);
    (x % 10) * pow10(count_digits(div_result)) + reverse_digits(div_result)
}

function pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function count_digits(x: int): int
  requires x >= 0
  decreases x
{
  if x < 10 then 1 else 1 + count_digits(x / 10)
}

lemma count_digits_nonneg(x: int)
  requires x >= 0
  ensures count_digits(x) >= 1
{
  if x < 10 {
  } else {
    count_digits_nonneg(x / 10);
  }
}

lemma count_digits_div_property(x: int)
  requires x >= 10
  ensures count_digits(x / 10) >= 0
{
  count_digits_nonneg(x / 10);
}

function is_palindrome(x: int): bool
  requires x >= 0
{
  x == reverse_digits(x)
}

method primePalindrome_866(n: int) returns (result: int)
  requires 1 <= n <= 100000000
  ensures -2147483648 <= result <= 2147483648
  ensures result >= n
  decreases *
{
  var current := n;
  
  while true
    invariant current >= n
    invariant current >= 1
    decreases *
  {
    if current >= 0 && current >= 2 && is_palindrome(current) && is_prime(current) {
      result := current;
      return;
    }
    
    if 10000000 < current < 100000000 {
      current := 100000000;
    } else {
      current := current + 1;
      if current > 2147483648 {
        result := n;
        return;
      }
    }
  }
}

method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483648
  ensures -2147483648 <= result <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp := x;
  
  while temp != 0
    invariant -2147483648 <= temp <= 2147483648
    invariant -2147483648 <= ans <= 2147483647
    decreases if temp >= 0 then temp else -temp
  {
    if ans < mi / 10 + 1 || ans > mx / 10 {
      result := 0;
      return;
    }
    
    var y := temp % 10;
    if temp < 0 && y > 0 {
      y := y - 10;
    }
    
    var new_ans := ans * 10 + y;
    if new_ans < -2147483648 || new_ans > 2147483647 {
      result := 0;
      return;
    }
    
    ans := new_ans;
    temp := (temp - y) / 10;
  }
  
  result := ans;
}

method main_3node_2(o: int) returns (result: int)
  requires 1 <= o <= 10000
  ensures -2147483648 <= result <= 2147483647
  decreases *
{
  var o1 := clumsy_1006(o);
  var o2 := primePalindrome_866(o1);
  var o3 := reverse_7(o2);
  result := o3;
}
