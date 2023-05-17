module PowModule {

  function Pow(b: int, e: nat): int {
    if e == 0 then 1 else b * Pow(b, e - 1)
  }

  method PowIter(b: int, e: nat) returns (r: int)
    ensures r == Pow(b, e)
  {
    r := 1;
    var i := 0;
    while i < e
      invariant i <= e
      invariant r == Pow(b, i)
    {
      r := r * b;
      i := i + 1;
    }
  }

  lemma Pow0(x: int)
    ensures Pow(x, 0) == 1
  {
  }

  lemma Pow1(x: int)
    ensures Pow(x, 1) == x
  {
  }

  lemma Pow2(x: int)
    ensures Pow(x, 2) == x * x
  {
    assert Pow(x, 2) == x * Pow(x, 1);
  }

  lemma PowBase0(y: nat)
    requires y > 0
    ensures Pow(0, y) == 0
  {
  }

  lemma PowMul(x: int, y: int, e: nat)
    ensures Pow(x * y, e) == Pow(x, e) * Pow(y, e)
  {
  }

  lemma PowExpAdd(x: int, a: nat, b: nat)
    ensures Pow(x, a + b) == Pow(x, a) * Pow(x, b)
  {
    if a > 0 {
      PowExpAdd(x, a - 1, b);
    }
  }

  function FastPow(b: int, e: nat): int
    decreases e
  {
    if e == 0 then 1 
    else if e % 2 == 0 then FastPow(b * b, e / 2)
    else b * FastPow(b, e - 1)
  }

  lemma FastPowEq(b: int, e: nat)
    ensures FastPow(b, e) == Pow(b, e)
    decreases e
  {
    if e == 0 {
    } else if e % 2 == 0 {
      calc {
        FastPow(b, e);
        FastPow(b * b, e / 2);
        { FastPowEq(b * b, e / 2); }
        Pow(b * b, e / 2);
        { PowMul(b, b, e / 2); }
        Pow(b, e / 2) * Pow(b, e / 2);
        { PowExpAdd(b, e / 2, e / 2); }
        Pow(b, e / 2 + e / 2);
      }
    }
  }

  method FastPowIter(b: int, e: nat) returns (r: int)
    ensures r == Pow(b, e)
  {
    r := 1;
    var x := b;
    var n := e;
    ghost var ex := 1;
    ghost var er := 0;
    while n > 0
      invariant e == n * ex + er
      invariant x == Pow(b, ex)
      invariant r == Pow(b, er)
    {
      if n % 2 != 0 {
        assert r * x == Pow(b, er + ex) by {
          calc {
            r * x;
            Pow(b, er) * Pow(b, ex);
            { PowExpAdd(b, er, ex); }
            Pow(b, er + ex);
          }
        }
        r := r * x;
        n := n - 1;
        er := er + ex;
      }
      assert x * x == Pow(b, ex + ex) by {
        calc {
          x * x;
          Pow(b, ex) * Pow(b, ex);
          { PowExpAdd(b, ex, ex); }
          Pow(b, ex + ex);
        }
      }
      assert n % 2 == 0;
      n := n / 2;
      x := x * x;
      ex := ex + ex;
    }
  }

}