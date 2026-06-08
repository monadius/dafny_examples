function Cons<T>(x: T, xs: seq<T>) : seq<T> {
    [x] + xs
}

function Map<A, B>(f: A -> B, xs: seq<A>): seq<B> {
  if |xs| == 0 then [] else Cons(f(xs[0]), Map(f, xs[1..]))
}

// Functor laws: https://wiki.haskell.org/Functor
// Functors must preserve identity morphisms
lemma MapIdentity<T>(xs : seq<T>)
ensures Map(x => x, xs) == xs
{
  if |xs| > 0 {
    MapIdentity(xs[1..]);
  }
}

// Functors preserve composition of morphisms
lemma MapCompose<A, B, C>(xs: seq<A>, f: B -> C, g: A -> B)
ensures Map(ys => f(g(ys)), xs) == Map(f, Map(g, xs))
{
  if |xs| > 0 {
    MapCompose(xs[1..], f, g);
  }
}