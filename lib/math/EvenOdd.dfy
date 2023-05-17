module EvenOdd {

  function Even(n: int): bool {
    n % 2 == 0
  }

  function Odd(n: int): bool {
    n % 2 != 0
  }

  lemma EvenMul2(k: int)
    ensures Even(2 * k)
  {
  }

  lemma OddMul2Plus1(k: int)
    ensures Odd(2 * k + 1)
  {
  }

  lemma Even1(n: int)
    requires Even(n)
    ensures Odd(n + 1)
    ensures Odd(n - 1)
  {
  }

  lemma Odd1(n: int)
    requires Odd(n)
    ensures Even(n + 1)
    ensures Even(n - 1)
  {
  }

  lemma EvenPlusEven(m: int, n: int)
    requires Even(m) && Even(n)
    ensures Even(m + n)
  {
  }

  lemma EvenPlusOdd(m: int, n: int)
    requires Even(m) && Odd(n)
    ensures Odd(m + n)
  {
  }

  lemma OddPlusOdd(m: int, n: int)
    requires Odd(m) && Odd(n)
    ensures Even(m + n)
  {
  }

  lemma EvenSpec(n: int)
    requires Even(n)
    ensures exists k :: n == 2 * k
  {
    assert n == 2 * (n / 2) + 0;
  }

  lemma OddSpec(n: int)
    requires Odd(n)
    ensures exists k :: n == 2 * k + 1
  {
    assert n == 2 * (n / 2) + 1;
  }
  
}