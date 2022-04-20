function Foldl'<A, B>(f: (A, B) -> A, z: A, xs: seq<B>): A {
  if |xs| == 0 then z else Foldl'(f, f(z, xs[0]), xs[1..])
}

// This definition is more convenient for loop specifications
function Foldl<A, B>(f: (A, B) -> A, z: A, xs: seq<B>): A {
  if |xs| == 0 then z else f(Foldl(f, z, xs[..|xs| - 1]), xs[|xs| - 1])
}

// method FoldlLoop<A, B>(f: (A, B) -> A, z: A, xs: seq<B>) returns (r: A) 
//   ensures r == Foldl(f, z, xs)
// {
//   r := z;
//   var i := 0;
//   while i < |xs|
//     invariant i <= |xs|
//     invariant r == Foldl(f, z, xs[..i])
//   {
//     r := f(r, xs[i]);
//     i := i + 1;
//     assert xs[..i] == xs[..i - 1] + [xs[i - 1]];
//   }
//   assert xs[..i] == xs;
// }

lemma Foldl'Concat<A, B>(f: (A, B) -> A, z: A, xs: seq<B>, ys: seq<B>)
  ensures Foldl'(f, z, xs + ys) == Foldl'(f, Foldl'(f, z, xs), ys)
{
  if |xs| == 0 {
    assert xs + ys == ys;
  } else {
    calc {
      Foldl'(f, z, xs + ys);
      { assert (xs + ys)[1..] == xs[1..] + ys; }
      Foldl'(f, f(z, xs[0]), xs[1..] + ys);
      { Foldl'Concat(f, f(z, xs[0]), xs[1..], ys); }
      Foldl'(f, Foldl'(f, f(z, xs[0]), xs[1..]), ys);
    }
  }
}

lemma FoldlEq<A, B>(f: (A, B) -> A, z: A, xs: seq<B>)
  ensures Foldl(f, z, xs) == Foldl'(f, z, xs)
{
  if |xs| > 0 {
    calc {
      Foldl'(f, z, xs);
      { assert xs == xs[..|xs| - 1] + [xs[|xs| - 1]]; }
      Foldl'(f, z, xs[..|xs| - 1] + [xs[|xs| - 1]]);
      { Foldl'Concat(f, z, xs[..|xs| - 1], [xs[|xs| - 1]]); }
      Foldl'(f, Foldl'(f, z, xs[..|xs| - 1]), [xs[|xs| - 1]]);
      Foldl'(f, Foldl(f, z, xs[..|xs| - 1]), [xs[|xs| - 1]]);
    }
  }
}

lemma FoldlConcat<A, B>(f: (A, B) -> A, z: A, xs: seq<B>, ys: seq<B>)
  ensures Foldl(f, z, xs + ys) == Foldl(f, Foldl(f, z, xs), ys)
{
  calc {
    Foldl(f, z, xs + ys);
    { FoldlEq(f, z, xs + ys); }
    Foldl'(f, z, xs + ys);
    { Foldl'Concat(f, z, xs, ys); }
    Foldl'(f, Foldl'(f, z, xs), ys);
    { FoldlEq(f, z, xs); FoldlEq(f, Foldl(f, z, xs), ys); }
    Foldl(f, Foldl(f, z, xs), ys);
  }
}