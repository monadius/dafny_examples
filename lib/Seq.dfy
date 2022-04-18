module Seq {

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