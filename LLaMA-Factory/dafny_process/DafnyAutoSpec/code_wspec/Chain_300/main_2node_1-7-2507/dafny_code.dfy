
method reverse_7(x: int) returns (result: int)
  requires -2147483648 <= x <= 2147483648
  ensures 0 <= result <= 2147483647
{
  var ans := 0;
  var mi := -2147483648;
  var mx := 2147483647;
  var current_x := x;
  
  while current_x != 0
    invariant mi == -2147483648
    invariant mx == 2147483647
    invariant 0 <= ans <= 2147483647
  {
    // Check for potential overflow
    if ans < mi / 10 + 1 || ans > mx / 10 {
      return 0;
    }
    
    var y := current_x % 10;
    if current_x < 0 && y > 0 {
      y := y - 10;
    }
    
    var new_ans := ans * 10 + y;
    if new_ans < 0 || new_ans > 2147483647 {
      return 0;
    }
    
    ans := new_ans;
    current_x := (current_x - y) / 10;
  }
  
  result := ans;
}

method smallestValue_2507(n: int) returns (result: int)
  requires 2 <= n <= 100000
  ensures result >= 2
  decreases *
{
  var current_n := n;
  
  while true
    invariant current_n >= 2
    decreases *
  {
    var t := current_n;
    var s := 0;
    var i := 2;
    var temp_n := current_n;
    
    // Factor current_n and sum the prime factors
    while i <= temp_n / i
      invariant 2 <= i
      invariant s >= 0
      invariant temp_n >= 1
    {
      while temp_n % i == 0
        invariant temp_n >= 1
        invariant i >= 2
        invariant s >= 0
        decreases temp_n
      {
        temp_n := temp_n / i;
        s := s + i;
      }
      i := i + 1;
    }
    
    // If temp_n > 1, it's a prime factor
    if temp_n > 1 {
      s := s + temp_n;
    }
    
    // Ensure s is at least 2
    if s < 2 {
      s := 2;
    }
    
    // If sum equals original value, we found the answer
    if s == t {
      return t;
    }
    
    current_n := s;
  }
}

method main_2node_1(o: int) returns (result: int)
  requires -2147483648 <= o <= 2147483648
  ensures result >= 2
  decreases *
{
  var o1 := reverse_7(o);
  
  // We need to ensure o1 is in valid range for smallestValue_2507
  if o1 < 2 {
    // If reverse_7 returns 0 or 1, we need a valid input for smallestValue_2507
    // Let's use 2 as the minimum valid input
    o1 := 2;
  } else if o1 > 100000 {
    // If o1 exceeds the upper bound, clamp it
    o1 := 100000;
  }
  
  var o2 := smallestValue_2507(o1);
  result := o2;
}
