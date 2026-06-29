include "../Seq.dfy"

module SeqCount {
  import opened Seq

  function Count<T(==)>(xs: seq<T>, v: T): nat {
    if |xs| == 0 then 0
    else (if xs[0] == v then 1 else 0) + Count(xs[1..], v)
  }

  lemma Count0<T>(xs: seq<T>, v: T)
    ensures Count(xs, v) == 0 <==> v !in xs
  {
  }

  lemma CountPos<T>(xs: seq<T>, v: T)
    ensures Count(xs, v) > 0 <==> v in xs
  {
  }

  lemma CountMultiset<T>(xs: seq<T>, v: T)
    ensures Count(xs, v) == multiset(xs)[v]
  {
    if |xs| > 0 {
      assert xs == [xs[0]] + xs[1..];
    }
  }

  lemma CountConcat<T>(xs: seq<T>, ys: seq<T>, v: T)
    ensures Count(xs + ys, v) == Count(xs, v) + Count(ys, v)
  {
    calc {
      Count(xs + ys, v);
      { CountMultiset(xs + ys, v); }
      multiset(xs + ys)[v];
      multiset(xs)[v] + multiset(ys)[v];
      { CountMultiset(xs, v); CountMultiset(ys, v); }
      Count(xs, v) + Count(ys, v);
    }
  }

  lemma CountFoldl<T>(xs: seq<T>, v: T)
    ensures Count(xs, v) == Foldl'((r, x) => (if x == v then 1 else 0) + r, 0, xs)
  {
    if |xs| > 0 {
      calc {
        Count(xs, v);
        { CountConcat(RemoveLast(xs), [Last(xs)], v); ConcatRemoveLastLast(xs); }
        Count(RemoveLast(xs), v) + Count([Last(xs)], v);
        Foldl'((r, x) => (if x == v then 1 else 0) + r, 0, RemoveLast(xs)) + (if Last(xs) == v then 1 else 0);
      }
    }
  }
}
