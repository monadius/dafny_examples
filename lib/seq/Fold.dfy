function Last<T>(xs: seq<T>): T
  requires 0 < |xs|
{
  xs[|xs| - 1]
}

function RemoveLast<T>(xs: seq<T>): seq<T>
  requires 0 < |xs|
{
  xs[..|xs| - 1]
}

function Foldl<A, B>(f: (A, B) -> A, z: A, xs: seq<B>): A {
  if |xs| == 0 then z else Foldl(f, f(z, xs[0]), xs[1..])
}

// This definition is more convenient for loop specifications
function Foldl'<A, B>(f: (A, B) -> A, z: A, xs: seq<B>): A {
  if |xs| == 0 then z else f(Foldl'(f, z, RemoveLast(xs)), Last(xs))
}

function Foldr<A, B>(f: (B, A) -> A, xs: seq<B>, z: A): A {
  if |xs| == 0 then z else f(xs[0], Foldr(f, xs[1..], z))
}

function Foldr'<A, B>(f: (B, A) -> A, xs: seq<B>, z: A): A {
  if |xs| == 0 then z else Foldr'(f, RemoveLast(xs), f(Last(xs), z))
}

// method FoldlIter<A, B>(f: (A, B) -> A, z: A, xs: seq<B>) returns (r: A)
//   ensures r == Foldl'(f, z, xs)
// {
//   var i := 0;
//   r := z;
//   while i < |xs|
//     invariant i <= |xs|
//     invariant r == Foldl'(f, z, xs[..i])
//   {
//     r := f(r, xs[i]);
//     assert xs[..i + 1] == xs[..i] + [xs[i]];
//     i := i + 1;
//   }
//   assert xs[..i] == xs;
// }

// method FoldlrIter<A, B>(f: (B, A) -> A, xs: seq<B>, z: A) returns (r: A)
//   ensures r == Foldr(f, xs, z)
// {
//   var i := |xs|;
//   r := z;
//   while i > 0
//     invariant i >= 0
//     invariant r == Foldr(f, xs[i..], z)
//   {
//     i := i - 1;
//     r := f(xs[i], r);
//   }
// }

// function Count<T>(xs: seq<T>, v: T): int {
//   // if |xs| == 0 then 0 else (if xs[0] == v then 1 else 0) + Count(xs[1..], v)
//   Foldr((x, n) => (if x == v then 1 else 0) + n, xs, 0)
// }

// method CountIter<T(==)>(xs: seq<T>, v: T) returns (n: int)
//   ensures n == Count(xs, v)
// {
//   n := 0;
//   var i := |xs|;
//   while i > 0
//     invariant i >= 0
//     invariant n == Count(xs[i..], v)
//   {
//     i := i - 1;
//     if xs[i] == v {
//       n := n + 1;
//     }
//   }
// }

predicate OpComm<T(==)>(f: (T, T) -> T, dom: seq<T>) {
  forall x, y :: x in dom && y in dom ==> f(x, y) == f(y, x)
}

ghost predicate OpAssoc<T(!new)>(f: (T, T) -> T) {
  forall x, y, z :: f(x, f(y, z)) == f(f(x, y), z)
}

ghost predicate OpNeutral<T(!new)>(f: (T, T) -> T, z: T) {
  forall x :: f(x, z) == f(z, x) == x
}

lemma FoldrEqFoldl<T(!new)>(f: (T, T) -> T, xs: seq<T>, z: T) 
  requires OpAssoc(f)
  requires OpNeutral(f, z)
  ensures Foldr(f, xs, z) == Foldl(f, z, xs)
{
  assume false;
}
