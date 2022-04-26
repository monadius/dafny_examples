include "Seq.dfy"
include "DivMod.dfy"

module DigitsModule {

  import opened Seq
  import DivMod

  // Verification of all lemmas is faster with {:opaque}
  function {:opaque} Digits(n: int, base: int): seq<int> 
    requires 2 <= base
  {
    if n <= 0 then [0] else if n < base then [n] else Digits(n / base, base) + [n % base]
  }

  lemma DigitsOne(n: int, base: int)
    requires 2 <= base
    ensures n < 0 ==> Digits(n, base) == [0]
    ensures 0 <= n < base ==> Digits(n, base) == [n]
  {
    reveal Digits();
  }

  lemma DigitsBound(n: int, base: int, i: int)
    requires 2 <= base
    requires 0 <= i < |Digits(n, base)|
    ensures 0 <= Digits(n, base)[i] < base
  {
    reveal Digits();
  }

  lemma DigitsSpec(n: int, base: int)
    requires 0 <= n && 2 <= base
    ensures Foldl'((r, d) => r * base + d, 0, Digits(n, base)) == n
    // ensures Foldl((r, d) => r * base + d, 0, Digits(n, base)) == n
  {
    reveal Digits();
    // FoldlEq((r, d) => r * base + d, 0, Digits(n, base));
  }

  lemma DigitsSplit(a: int, b: int, base: int)
    requires 2 <= base
    requires 0 < a && 0 <= b < base
    ensures Digits(a * base + b, base) == Digits(a, base) + [b]
  {
    DivMod.DivModMulAdd(a, base, b);
    reveal Digits();
  }

  lemma DigitsNoLeading0(a: int, base: int)
    requires 2 <= base
    requires 0 < a
    ensures 0 < |Digits(a, base)|
    ensures 0 < Digits(a, base)[0]
  {
    reveal Digits();
  }

}