include "DivMod.dfy"

function method Abs(x: int): int {
  if x < 0 then -x else x
}

lemma AbsProps(x: int)
  ensures 0 <= Abs(x)
  ensures -Abs(x) <= x <= Abs(x)
  ensures Abs(x) == x || Abs(x) == -x
  ensures Abs(-x) == Abs(x)
{
}

lemma AbsBound(x: int, y: int)
  ensures Abs(x) <= y <==> -y <= x <= y
{
}

lemma AbsAddIneq(x: int, y: int)
  ensures Abs(x + y) <= Abs(x) + Abs(y)
{
}

lemma AbsMul(x: int, y: int)
  ensures Abs(x * y) == Abs(x) * Abs(y)
{
}

// lemma AbsDiv(x: int, y: int)
//   requires y != 0
//   ensures Abs(x / y) == Abs(x) / Abs(y)
// {
//   assert Abs(x / y) * Abs(y) == Abs(x) by {
    
//   }
//   // DivMod.DivModSpec(Abs(x), Abs(y), Abs(x) / Abs(y), 0);
//   assume false;
// }