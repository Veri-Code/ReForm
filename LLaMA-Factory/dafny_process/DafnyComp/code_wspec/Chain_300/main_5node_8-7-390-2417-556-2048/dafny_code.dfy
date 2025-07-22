
method reverse_7(x: int) returns (ans: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= ans <= 1000000000
{
  ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var temp_x := x;
  
  while temp_x != 0
    invariant ans >= 0
    invariant ans <= 1000000000
    decreases if temp_x >= 0 then temp_x else -temp_x
  {
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := temp_x % 10;
    if temp_x < 0 && y > 0 {
      y := y - 10;
    }
    
    var new_ans := ans * 10 + y;
    if new_ans < 0 || new_ans > 1000000000 {
      return 0;
    }
    ans := new_ans;
    temp_x := (temp_x - y) / 10;
  }
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 1000000000
{
  var a1 := 1;
  var an := n;
  var i := 0;
  var step := 1;
  var cnt := n;
  
  while cnt > 1
    invariant cnt >= 1
    invariant step >= 1
    invariant step <= n
    invariant a1 >= 1 && an >= 1
    invariant a1 <= n && an <= n
    decreases cnt
  {
    if i % 2 == 1 {
      an := an - step;
      if an < 1 {
        an := 1;
      }
      if cnt % 2 == 1 && a1 + step <= n {
        a1 := a1 + step;
      }
    } else {
      if a1 + step <= n {
        a1 := a1 + step;
      }
      if cnt % 2 == 1 {
        an := an - step;
        if an < 1 {
          an := 1;
        }
      }
    }
    cnt := cnt / 2;
    if step <= n / 2 {
      step := step * 2;
    }
    i := i + 1;
  }
  
  result := a1;
}

method countDigits(n: int) returns (count: int, oddCount: int, evenCount: int)
  requires n >= 1
  ensures count >= 1
  ensures oddCount >= 0 && evenCount >= 0
  ensures oddCount + evenCount == count
{
  count := 0;
  oddCount := 0;
  evenCount := 0;
  var temp := n;
  
  while temp > 0
    invariant oddCount >= 0 && evenCount >= 0
    invariant oddCount + evenCount == count
    invariant count >= 0
    invariant temp >= 0
    invariant temp == 0 ==> count >= 1
    decreases temp
  {
    var digit := temp % 10;
    if digit % 2 == 1 {
      oddCount := oddCount + 1;
    } else {
      evenCount := evenCount + 1;
    }
    count := count + 1;
    temp := temp / 10;
  }
}

function power10(exp: int): int
  requires 0 <= exp <= 9
  ensures power10(exp) >= 1
{
  if exp == 0 then 1
  else 10 * power10(exp - 1)
}

method closestFair_2417(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures 1 <= result <= 2147483648
  decreases 2147483648 - n
{
  var digitCount, oddCount, evenCount := countDigits(n);
  
  if digitCount % 2 == 1 {
    if digitCount <= 9 {
      var x := power10(digitCount);
      var halfDigits := digitCount / 2;
      var y := 0;
      if halfDigits > 0 && halfDigits <= 9 {
        y := power10(halfDigits) - 1;
        if halfDigits > 0 && halfDigits - 1 >= 0 && halfDigits - 1 <= 9 {
          y := y * (power10(halfDigits) / power10(halfDigits - 1));
        }
      }
      result := x + y;
    } else {
      result := 1000000000;
    }
  } else if oddCount == evenCount {
    result := n;
  } else {
    if n < 1000000000 {
      result := closestFair_2417(n + 1);
    } else {
      result := 1000000000;
    }
  }
}

method nextGreaterElement_556(n: int) returns (result: int)
  requires 1 <= n <= 2147483648
  ensures -1 <= result <= 1000000
{
  var s := [];
  var temp := n;
  
  // Convert number to digit sequence
  while temp > 0
    decreases temp
  {
    s := [temp % 10] + s;
    temp := temp / 10;
  }
  
  if |s| == 0 {
    return -1;
  }
  
  var len := |s|;
  var i := len - 2;
  
  // Find rightmost digit that is smaller than the digit next to it
  while i >= 0 && s[i] >= s[i + 1]
    invariant -1 <= i < len
    decreases i + 1
  {
    i := i - 1;
  }
  
  if i < 0 {
    return -1;
  }
  
  // Find the smallest digit on right side of above character that is greater than s[i]
  var j := len - 1;
  while s[i] >= s[j]
    invariant i < j < len
    decreases j - i
  {
    j := j - 1;
  }
  
  // Swap
  var temp_digit := s[i];
  s := s[i := s[j]];
  s := s[j := temp_digit];
  
  // Reverse the suffix starting at s[i+1]
  var left := i + 1;
  var right := len - 1;
  while left < right
    invariant i + 1 <= left <= right + 1 <= len
    invariant 0 <= left < |s|
    invariant 0 <= right < |s|
    decreases right - left
  {
    temp_digit := s[left];
    s := s[left := s[right]];
    s := s[right := temp_digit];
    left := left + 1;
    right := right - 1;
  }
  
  // Convert back to number
  var ans := 0;
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant ans >= 0
    invariant ans <= 1000000
    decreases |s| - k
  {
    if ans > 100000 {
      return -1;
    }
    var new_ans := ans * 10 + s[k];
    if new_ans < 0 || new_ans > 1000000 {
      return -1;
    }
    ans := new_ans;
    k := k + 1;
  }
  
  if ans > 2147483647 {
    result := -1;
  } else {
    result := ans;
  }
}

method isBeautiful(x: int) returns (beautiful: bool)
  requires x >= 1
{
  var cnt := new int[10];
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    cnt[i] := 0;
    i := i + 1;
  }
  
  var y := x;
  while y > 0
    decreases y
  {
    var digit := y % 10;
    cnt[digit] := cnt[digit] + 1;
    y := y / 10;
  }
  
  beautiful := true;
  i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    if cnt[i] != 0 && i != cnt[i] {
      beautiful := false;
      break;
    }
    i := i + 1;
  }
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures result >= 1
{
  var x := n + 1;
  while x <= 10000000
    invariant x >= n + 1
    decreases 10000000 - x
  {
    var beautiful := isBeautiful(x);
    if beautiful {
      result := x;
      return;
    }
    x := x + 1;
  }
  result := 1; // fallback
}

method main_5node_8(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures result >= 1
{
  var o1 := reverse_7(o);
  if o1 == 0 {
    result := 1;
    return;
  }
  
  var o2 := lastRemaining_390(o1);
  var o3 := closestFair_2417(o2);
  
  var o4 := nextGreaterElement_556(o3);
  if o4 == -1 {
    result := 1;
    return;
  }
  
  var o5 := nextBeautifulNumber_2048(o4);
  result := o5;
}
