include "../Seq.dfy"
include "../math/DivMod.dfy"

module DigitsModule {

  import opened Seq
  import DivMod

  // Verification of all lemmas is faster with {:opaque}
  function {:opaque} Digits(n: int, base: int): seq<int>
    requires 2 <= base
    decreases n * 1
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

  lemma DigitsBound(n: int, base: int)
    requires 2 <= base
    decreases n
    ensures forall i :: 0 <= i < |Digits(n, base)| ==> 0 <= Digits(n, base)[i] < base
  {
    reveal Digits();
    if n >= base {
      assert n / base < n;
      DigitsBound(n/base, base);
      assert Digits(n,base) == Digits(n/base, base) + [n%base];
    }
  }

  lemma DigitsSpec(n: int, base: int)
    requires 0 <= n && 2 <= base
    ensures Foldl'((r, d) => r * base + d, 0, Digits(n, base)) == n
    decreases n
    // ensures Foldl((r, d) => r * base + d, 0, Digits(n, base)) == n
  {
    reveal Digits();
    if n >= base {
      assert n / base < n;
      DigitsSpec(n / base, base);
      assert |Digits(n / base, base) + [n % base]| >= 1;
      assert RemoveLast(Digits(n / base, base) + [n % base]) == Digits(n / base, base) by {
        RemoveLastAppend(Digits(n / base, base), n % base);
      }
      assert Last(Digits(n / base, base) + [n % base]) == n % base by {
        LastAppend(Digits(n / base, base), n % base);
      }
      calc ==
      {
        Foldl'((r, d) => r * base + d, 0, Digits(n, base));
        Foldl'((r, d) => r * base + d, 0, Digits(n / base, base) + [n % base]);
        Foldl'((r, d) => r * base + d, 0, RemoveLast(Digits(n / base, base) + [n % base]))*base + Last(Digits(n / base, base) + [n % base]);
        Foldl'((r, d) => r * base + d, 0, Digits(n / base, base))*base +  (n % base);
      }
    }
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
    decreases a
  {
    reveal Digits();
    if a < base {

    } else {
      assert a / base < a;
      DigitsNoLeading0(a/base, base);
      assert Digits(a, base)[0] == Digits(a / base, base)[0];
    }
  }
}
