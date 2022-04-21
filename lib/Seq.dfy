module Seq {

  /***** Reverse *****/

  function Reverse<T>(xs: seq<T>): seq<T> {
    if |xs| == 0 then xs else Reverse(xs[1..]) + [xs[0]]
  }

  lemma ReverseLength<T>(xs: seq<T>)
    ensures |Reverse(xs)| == |xs|
  {
    // reveal Reverse();
  }

  lemma ReverseMem<T>(xs: seq<T>)
    ensures forall x {:trigger x in Reverse(xs)} :: x in Reverse(xs) <==> x in xs
  {
    // reveal Reverse();
  }

  lemma ReverseIndexAll<T>(xs: seq<T>)
    ensures |Reverse(xs)| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> Reverse(xs)[i] == xs[|xs| - i - 1]
  {
    // reveal Reverse();
  }

  lemma ReverseIndex<T>(xs: seq<T>, i: int)
    requires 0 <= i < |xs|
    ensures |Reverse(xs)| == |xs|
    ensures Reverse(xs)[i] == xs[|xs| - i - 1]
  {
    ReverseIndexAll(xs);
    assert forall i :: 0 <= i < |xs| ==> Reverse(xs)[i] == xs[|xs| - i - 1];
  }

  lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
    requires |xs| == |ys|
    requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
    ensures xs == ys
  {
  }

  lemma ReverseReverse<T>(xs: seq<T>)
    ensures Reverse(Reverse(xs)) == xs
  {
    ReverseIndexAll(Reverse(xs));
    ReverseIndexAll(xs);
    SeqEq(Reverse(Reverse(xs)), xs);
  }

  lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
    ensures Reverse(xs + ys) == Reverse(ys) + Reverse(xs)
  {
    // reveal Reverse();
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      assert xs + ys == [xs[0]] + (xs[1..] + ys);
    }
  }

  /***** Foldl *****/

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

  // method FilterMethod(xs: seq<int>, f: int -> bool) returns (ys: seq<int>) 
  //   ensures forall y :: y in ys ==> f(y)
  //   ensures forall x :: x in xs && f(x) ==> x in ys
  // {
  //   var i := 0;
  //   ys := [];
  //   while i < |xs|
  //     invariant 0 <= i <= |xs|
  //     invariant forall x :: x in xs[..i] && f(x) ==> x in ys
  //     invariant forall y :: y in ys ==> f(y)
  //   {
  //     if f(xs[i]) {
  //       ys := ys + [xs[i]];
  //     }
  //     i := i + 1;
  //   }
  // }

  // function Filter(xs: seq<int>, f: int -> bool): seq<int>
  //   ensures forall y :: y in Filter(xs, f) ==> f(y)
  //   ensures forall x :: x in xs && f(x) ==> x in Filter(xs, f)
  // {
  //   if |xs| == 0 then [] 
  //   else if f(xs[0]) then [xs[0]] + Filter(xs[1..], f)
  //   else Filter(xs[1..], f)
  // }

  /***** Sorted for seq<int> *****/

  predicate Sorted(xs: seq<int>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  }

  predicate Sorted1(xs: seq<int>) {
    forall i :: 0 <= i < |xs| - 1 ==> xs[i] <= xs[i + 1]
  }

  lemma SortedEq1(xs: seq<int>) 
    ensures Sorted(xs) <==> Sorted1(xs)
  {
    if |xs| > 0 {
      SortedEq1(xs[1..]);
      forall i | Sorted1(xs) && 1 <= i < |xs| ensures xs[0] <= xs[i] {
        assert xs[0] <= xs[1];
      }
    }
  }

  predicate SortedStrict(xs: seq<int>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
  }

  predicate SortedStrict1(xs: seq<int>) {
    forall i :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i + 1]
  }

  lemma SortedStrictEq1(xs: seq<int>) 
    ensures SortedStrict(xs) <==> SortedStrict1(xs)
  {
    if |xs| > 0 {
      SortedStrictEq1(xs[1..]);
      forall i | SortedStrict1(xs) && 1 <= i < |xs| ensures xs[0] < xs[i] {
        assert xs[0] < xs[1];
      }
    }
  }

  predicate IsSuffix<T>(xs: seq<T>, ys: seq<T>) {
    |xs| <= |ys| && xs == ys[|ys| - |xs|..]
  }

}