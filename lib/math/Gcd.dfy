include "Abs.dfy"

function {:opaque} Gcd(a: int, b: int): int
  decreases Abs(b)
{
  if b == 0 then Abs(a) else Gcd(b, a % b)
}

lemma GcdPos(a: int, b: int)
  requires a != 0 || b != 0
  ensures 0 < Gcd(a, b)
  decreases Abs(b)
{
  reveal Gcd();
}

lemma Gcd0(a: int, b: int)
  ensures Gcd(a, b) == 0 <==> a == 0 && b == 0
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
  requires a != 0 || b != 0
  ensures 0 < Gcd(a, b) && a % Gcd(a, b) == 0 && b % Gcd(a, b) == 0
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