include "Abs.dfy"

function method {:opaque} Gcd(a: int, b: int): int
  decreases Abs(b)
{
  if b != 0 then Gcd(b, a % b) else if a == 0 then 1 else Abs(a)
}

lemma Gcd00()
  ensures Gcd(0, 0) == 1
{
  reveal Gcd();
}

lemma GcdPos(a: int, b: int)
  ensures 0 < Gcd(a, b)
  decreases Abs(b)
{
  reveal Gcd();
}

lemma MulMod(a: int, b: int, c: int)
  requires c != 0
  ensures (a * b) % c == (a % c) * (b % c) % c

lemma AddMod(a: int, b: int, c: int)
  requires c != 0
  ensures (a + b) % c == (a % c + b % c) % c

lemma GcdIsDivisor(a: int, b: int)
  ensures 0 < Gcd(a, b)
  ensures a % Gcd(a, b) == 0 && b % Gcd(a, b) == 0
  // ensures forall c :: c != 0 && a % c == 0 && b % c == 0 ==> Gcd(a, b) % c == 0
  decreases Abs(b)
{
  if b == 0 {
    reveal Gcd();
  } else {
    assert Gcd(a, b) == Gcd(b, a % b) by {
      reveal Gcd();
    }
    GcdIsDivisor(b, a % b);
    assert b % Gcd(a, b) == 0;
    assert (a % b) % Gcd(a, b) == 0;
    calc {
      a % Gcd(a, b);
      (a / b * b + a % b) % Gcd(a, b);
      { AddMod(a / b * b, a % b, Gcd(a, b)); }
      (a / b * b % Gcd(a, b) + (a % b) % Gcd(a, b)) % Gcd(a, b);
      { MulMod(a / b, b, Gcd(a, b)); }
      (a / b % Gcd(a, b) * (b % Gcd(a, b)) % Gcd(a, b) + 0) % Gcd(a, b);
      (a / b % Gcd(a, b) * 0 % Gcd(a, b)) % Gcd(a, b);
      0;
    }
  }
}

lemma GcdSym(a: int, b: int)
  ensures Gcd(a, b) == Gcd(b, a)
  decreases Abs(b)
// {
//   if b == 0 || a == 0 {
//     reveal Gcd();
//   } else {
//     assert Gcd(a, b) == Gcd(b, a % b) by {
//       reveal Gcd();
//     }
//     assert Gcd(b, a) == Gcd(a, b % a) by {
//       reveal Gcd();
//     }
//     GcdSym(b, a % b);
//     GcdSym(a, b % a);
//     assert Gcd(b, a % b) == Gcd(a % b, b);
//   }
// }
