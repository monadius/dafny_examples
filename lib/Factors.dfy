include "Seq.dfy"

module FactorsModule {
  
  import opened Seq

  function AllFactorsSet(n: int): set<int> {
    set d | 1 <= d <= n && n % d == 0 :: d
  }

  // Returns all positive factors of a number n below or equal to the given bound d.
  function Factors(n: int, d: int): seq<int> {
    if d < 1 then [] else Factors(n, d - 1) + (if n % d == 0 then [d] else [])
  }

  // All factors of a positive number n (returns [] for non-positive numbers).
  function AllFactors(n: int): seq<int> {
    Factors(n, n)
  }

  lemma InFactors(n: int, d: int, x: int)
    ensures x in Factors(n, d) <==> 1 <= x <= d && n % x == 0
  {
    if d > 0 {
      assert x in Factors(n, d - 1) ==> 1 <= x <= d && n % x == 0;
    }
  }

  lemma InAllFactors(n: int, x: int)
    requires n >= 1
    ensures x in AllFactors(n) ==> 1 <= x <= n && n % x == 0
    ensures 1 <= x && n % x == 0 ==> x in AllFactors(n)
  {
    InFactors(n, n, x);
  }

  lemma FactorsSortedStrict(n: int, d: int)
    ensures SortedStrict(Factors(n, d))
  {
    if (d > 0) {
      if n % d == 0 {
        forall x | x in Factors(n, d - 1) ensures x < d {
          InFactors(n, d - 1, x);
        }
      }
    }
  }

  lemma FactorsDistinct(n: int, d: int)
    ensures Distinct(Factors(n, d))
  {
    FactorsSortedStrict(n, d);
    SortedStrictImpDistinct(Factors(n, d));
  }

  lemma AllFactorsNonPos(n: int)
    requires n <= 0
    ensures AllFactors(n) == []
  {
  }

  lemma OneInFactors(n: int, d: int)
    requires d >= 1
    ensures 1 <= |Factors(n, d)| && Factors(n, d)[0] == 1
  {
  }

  // function Factors2(n: int, d: int): seq<int> 
  //   requires n >= 1
  // {
  //   Filter(seq(n, i => i + 1), d => d > 0 && n % d == 0)
  // }

  // method FindFactors(n: int) returns (factors: seq<int>)
  //   requires n >= 1
  //   ensures factors == Factors(n, n)
  // {
  //   var d := 1;
  //   factors := [];
  //   while d <= n
  //     invariant 1 <= d <= n + 1
  //     invariant factors == Factors(n, d - 1)
  //   {
  //     if n % d == 0 {
  //       factors := factors + [d];
  //     }
  //     d := d + 1;
  //   }
  // }

  lemma FactorsGtN(n: int, d: int)
    requires n >= 1
    requires d >= n
    ensures Factors(n, d) == AllFactors(n)
  {
  }

  // lemma {:induction a} FactorsPrefix(n: int, a: int, b: int)
  //   requires a <= b
  //   ensures Factors(n, a) <= Factors(n, b)
  //   decreases b - a
  // {
  //   if a < b {
  //     assert Factors(n, a + 1) <= Factors(n, b);
  //   }
  // }

  lemma FactorsPrefix(n: int, a: int, b: int)
    requires a <= b
    ensures Factors(n, a) <= Factors(n, b)
  {
    if a < 1 {
    } else {
      var factors := Factors(n, a);
      var i := a + 1;
      while i <= b
        invariant i <= b + 1
        invariant factors == Factors(n, i - 1)
        invariant Factors(n, a) <= factors
      {
        if n % i == 0 {
          factors := factors + [i];
        }
        i := i + 1;
      }
    }
  }

  lemma FactorsPrefixIndex(n: int, d: int, i: int)
    requires 0 <= i < |Factors(n, d)| <= |AllFactors(n)|
    ensures Factors(n, d)[i] == AllFactors(n)[i]
  {
    if d <= n {
      FactorsPrefix(n, d, n);
    }
  }

  lemma AllFactorsSymmetric(n: int, i: int)
    requires 0 <= i < |AllFactors(n)|
    ensures AllFactors(n)[i] > 0
    ensures AllFactors(n)[|AllFactors(n)| - i - 1] == n / AllFactors(n)[i]


}