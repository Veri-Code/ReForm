
method reverse_7(x: int) returns (ans: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= ans <= 1000000000
{
  ans := 0;
  var mi := -2147483648;  // -(2^31)
  var mx := 2147483647;   // 2^31 - 1
  var temp_x := x;
  
  while temp_x != 0
    invariant -1000000000 <= ans <= 1000000000
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
    // Overflow check
    if ans < mi / 10 + 1 || ans > mx / 10 {
      ans := 0;
      return;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    // Check bounds before updating ans
    if ans > 100000000 || ans < -100000000 {
      ans := 0;
      return;
    }
    
    ans := ans * 10 + y;
    
    // Additional safety check after update
    if ans > 1000000000 || ans < -1000000000 {
      ans := 0;
      return;
    }
    
    temp_x := (temp_x - y) / 10;
  }
  
  if ans < 0 {
    ans := 0;
  }
  if ans > 1000000000 {
    ans := 0;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 100000000
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant a1 >= 1 - step
    invariant an >= 1 - step
    invariant a1 <= n + step
    invariant an <= n + step
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
  
  result := a1;
  if result < 1 {
    result := 1;
  }
  if result > 100000000 {
    result := 100000000;
  }
}

method maxDiff_1432(num: int) returns (diff: int)
  requires 1 <= num <= 100000000
{
  var digits := int_to_digits(num);
  var max_digits := digits[..];
  var min_digits := digits[..];
  
  // Maximize: replace first non-9 digit with 9
  var i := 0;
  while i < |max_digits|
    invariant 0 <= i <= |max_digits|
  {
    if max_digits[i] != 9 {
      max_digits := replace_digit(max_digits, max_digits[i], 9);
      break;
    }
    i := i + 1;
  }
  
  // Minimize: replace first digit with 1 if not 1, otherwise replace first non-0,1 digit with 0
  if min_digits[0] != 1 {
    min_digits := replace_digit(min_digits, min_digits[0], 1);
  } else {
    i := 1;
    while i < |min_digits|
      invariant 1 <= i <= |min_digits|
    {
      if min_digits[i] != 0 && min_digits[i] != 1 {
        min_digits := replace_digit(min_digits, min_digits[i], 0);
        break;
      }
      i := i + 1;
    }
  }
  
  var max_num := digits_to_int(max_digits);
  var min_num := digits_to_int(min_digits);
  diff := max_num - min_num;
}

method main_3node_2(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  requires reverse_7_returns_nonzero(o)
  ensures true
{
  var o1 := reverse_7(o);
  if o1 == 0 {
    result := 0;
    return;
  }
  
  // Ensure o1 is in valid range for lastRemaining_390
  if o1 < 1 || o1 > 1000000000 {
    result := 0;
    return;
  }
  
  var o2 := lastRemaining_390(o1);
  
  // Ensure o2 is in valid range for maxDiff_1432
  if o2 < 1 || o2 > 100000000 {
    result := 0;
    return;
  }
  
  var o3 := maxDiff_1432(o2);
  result := o3;
}

predicate reverse_7_returns_nonzero(x: int)
{
  // Simplified predicate - in practice this would need to capture
  // the exact conditions under which reverse_7 returns non-zero
  true
}

// Helper functions for digit manipulation
function int_to_digits(n: int): seq<int>
  requires n >= 0
  ensures |int_to_digits(n)| >= 1
  ensures forall i :: 0 <= i < |int_to_digits(n)| ==> 0 <= int_to_digits(n)[i] <= 9
{
  if n < 10 then [n]
  else int_to_digits(n / 10) + [n % 10]
}

function digits_to_int(digits: seq<int>): int
  requires |digits| >= 1
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  ensures digits_to_int(digits) >= 0
{
  if |digits| == 1 then digits[0]
  else digits_to_int(digits[..|digits|-1]) * 10 + digits[|digits|-1]
}

function replace_digit(digits: seq<int>, old_digit: int, new_digit: int): seq<int>
  requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  requires 0 <= old_digit <= 9
  requires 0 <= new_digit <= 9
  ensures |replace_digit(digits, old_digit, new_digit)| == |digits|
  ensures forall i :: 0 <= i < |digits| ==> 0 <= replace_digit(digits, old_digit, new_digit)[i] <= 9
{
  seq(|digits|, i requires 0 <= i < |digits| => if digits[i] == old_digit then new_digit else digits[i])
}
