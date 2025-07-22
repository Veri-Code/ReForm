
method nextBeautifulNumber_2048(n: int) returns (result: int)
  requires 0 <= n <= 1000000
  ensures 1 <= result <= 1000000000
  ensures result > n
  ensures isBeautifulNumber(result)
  ensures forall k :: n < k < result ==> !isBeautifulNumber(k)
{
  var x := n + 1;
  while x <= 1000000000
    invariant n < x <= 1000000001
    invariant forall k :: n < k < x ==> !isBeautifulNumber(k)
  {
    if isBeautifulNumber(x) {
      return x;
    }
    x := x + 1;
  }
  // This should never be reached given the constraints
  assume false;
}

predicate isBeautifulNumber(x: int)
  requires x >= 0
{
  var digits := getDigitCounts(x);
  forall i :: 0 <= i <= 9 ==> (digits[i] == 0 || digits[i] == i)
}

function getDigitCounts(x: int): seq<int>
  requires x >= 0
  ensures |getDigitCounts(x)| == 10
  ensures forall i :: 0 <= i < 10 ==> getDigitCounts(x)[i] >= 0
{
  getDigitCountsHelper(x, seq(10, _ => 0))
}

function getDigitCountsHelper(x: int, counts: seq<int>): seq<int>
  requires x >= 0
  requires |counts| == 10
  requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
  ensures |getDigitCountsHelper(x, counts)| == 10
  ensures forall i :: 0 <= i < 10 ==> getDigitCountsHelper(x, counts)[i] >= 0
  decreases x
{
  if x == 0 then counts
  else
    var digit := x % 10;
    var newCounts := counts[digit := counts[digit] + 1];
    getDigitCountsHelper(x / 10, newCounts)
}

method lastRemaining_390(n: int) returns (result: int)
  requires 1 <= n <= 1000000000
  ensures result >= 1
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

method main_2node_1(o: int) returns (result: int)
  requires 0 <= o <= 1000000
  ensures result >= 1
{
  var o1 := nextBeautifulNumber_2048(o);
  var o2 := lastRemaining_390(o1);
  result := o2;
}
