include "../lib/Digits.dfy"
include "../lib/Seq.dfy"

import opened Seq
import opened DigitsModule

predicate NumericPalindrome(n: int)
  requires 0 <= n
{
  Digits(n, 10) == Reverse(Digits(n, 10))
}

method ReverseNumber(n: int) returns (r: int)
  requires 0 <= n
  // ensures Digits(r, 10) == Reverse(Digits(n, 10))
{
  r := 0;
  var x := n;
  ghost var b := 1;
  ghost var y := 0;
  assert Digits(r, 10) == Reverse(Digits(y, 10)) by {
    reveal Digits();
  }
  while x > 0
    invariant 0 <= r
    invariant 0 <= x
    invariant 1 <= b
    invariant y == n % b
    invariant Digits(r, 10) == Reverse(Digits(y, 10))
  {
    ghost var oldR := r;
    ghost var oldY := y;
    r := r * 10 + x % 10;
    y := y + x % 10 * b;
    b := b * 10;
    assume y == n % b;
    assert Digits(r, 10) == (if oldR > 0 then Digits(oldR, 10) else []) + [x % 10] by {
      if oldR > 0 {
        DigitsSplit(oldR, x % 10, 10);
      } else {
        DigitsOne(r, 10);
      }
    }
    // assume Digits(r, 10) == oldR + [x % 10];
    // assume Digits(y, 10) == [x % 10] + (if oldY > 0 then ;
    x := x / 10;
  }
}

// method IsPalindrome(n: int) returns (r: bool)
//   requires 0 <= n
//   ensures r == true ==> NumericPalindrome(n)
// {

// }