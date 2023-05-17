module MinMax {

  function Min(a: int, b: int): int {
    if a <= b then a else b
  }

  function Max(a: int, b: int): int {
    if a >= b then a else b
  }

  lemma MinProps(a: int, b: int)
    ensures Min(a, b) <= a
    ensures Min(a, b) <= b
    ensures Min(a, b) == a || Min(a, b) == b
    // ensures forall x :: x <= a && x <= b ==> x <= Min(a, b)
  {
  }

  lemma MaxProps(a: int, b: int)
    ensures a <= Max(a, b)
    ensures b <= Max(a, b)
    ensures Max(a, b) == a || Max(a, b) == b
    // ensures forall x :: a <= x && b <= x ==> Max(a, b) <= x
  {
  }

  lemma MinEqMax(a: int, b: int)
    requires Min(a, b) == Max(a, b)
    ensures a == b
  {
  }
  
}