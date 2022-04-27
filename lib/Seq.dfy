module Seq {

  /***** Last *****/

  function method Last<T>(xs: seq<T>): T
    requires 0 < |xs|
  {
    xs[|xs| - 1]
  }

  function method RemoveLast<T>(xs: seq<T>): seq<T>
    requires 0 < |xs|
  {
    xs[..|xs| - 1]
  }

  lemma ConcatRemoveLastLast<T>(xs: seq<T>)
    requires 0 < |xs|
    ensures RemoveLast(xs) + [Last(xs)] == xs
  {
  }

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

  function Foldl<A, B>(f: (A, B) -> A, z: A, xs: seq<B>): A {
    if |xs| == 0 then z else Foldl(f, f(z, xs[0]), xs[1..])
  }

  // This definition is more convenient for loop specifications
  function Foldl'<A, B>(f: (A, B) -> A, z: A, xs: seq<B>): A {
    if |xs| == 0 then z else f(Foldl'(f, z, xs[..|xs| - 1]), xs[|xs| - 1])
  }

  lemma FoldlConcat<A, B>(f: (A, B) -> A, z: A, xs: seq<B>, ys: seq<B>)
    ensures Foldl(f, z, xs + ys) == Foldl(f, Foldl(f, z, xs), ys)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        Foldl(f, z, xs + ys);
        { assert (xs + ys)[1..] == xs[1..] + ys; }
        Foldl(f, f(z, xs[0]), xs[1..] + ys);
        { FoldlConcat(f, f(z, xs[0]), xs[1..], ys); }
        Foldl(f, Foldl(f, f(z, xs[0]), xs[1..]), ys);
      }
    }
  }

  lemma FoldlEq<A, B>(f: (A, B) -> A, z: A, xs: seq<B>)
    ensures Foldl'(f, z, xs) == Foldl(f, z, xs)
  {
    if |xs| > 0 {
      calc {
        Foldl(f, z, xs);
        { assert xs == xs[..|xs| - 1] + [xs[|xs| - 1]]; }
        Foldl(f, z, xs[..|xs| - 1] + [xs[|xs| - 1]]);
        { FoldlConcat(f, z, xs[..|xs| - 1], [xs[|xs| - 1]]); }
        Foldl(f, Foldl(f, z, xs[..|xs| - 1]), [xs[|xs| - 1]]);
        Foldl(f, Foldl'(f, z, xs[..|xs| - 1]), [xs[|xs| - 1]]);
      }
    }
  }

  lemma Foldl'Concat<A, B>(f: (A, B) -> A, z: A, xs: seq<B>, ys: seq<B>)
    ensures Foldl'(f, z, xs + ys) == Foldl'(f, Foldl'(f, z, xs), ys)
  {
    calc {
      Foldl'(f, z, xs + ys);
      { FoldlEq(f, z, xs + ys); }
      Foldl(f, z, xs + ys);
      { FoldlConcat(f, z, xs, ys); }
      Foldl(f, Foldl(f, z, xs), ys);
      { FoldlEq(f, z, xs); FoldlEq(f, Foldl(f, z, xs), ys); }
      Foldl'(f, Foldl'(f, z, xs), ys);
    }
  }

  function Sum(xs: seq<int>): int {
    Foldl'((a, b) => a + b, 0, xs)
  }

  lemma SumConcat(xs: seq<int>, ys: seq<int>)
    ensures Sum(xs + ys) == Sum(xs) + Sum(ys)
  {
    if |ys| == 0 {
      assert xs + ys == xs;
    } else {
      assert xs + ys == (xs + RemoveLast(ys)) + [Last(ys)];
      SumConcat(xs, RemoveLast(ys));
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

  /***** Distinct *****/

  predicate Distinct<T>(xs: seq<T>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
  }

  predicate DistinctRec<T>(xs: seq<T>) {
    if |xs| == 0 then true else xs[0] !in xs[1..] && DistinctRec(xs[1..])
  }

  predicate DistinctRecLast<T>(xs: seq<T>) {
    if |xs| == 0 then true else Last(xs) !in RemoveLast(xs) && DistinctRecLast(RemoveLast(xs))
  }

  lemma DistinctEqRec<T>(xs: seq<T>)
    ensures Distinct(xs) <==> DistinctRec(xs)
  {
  }

  lemma DistinctEqRecLast<T>(xs: seq<T>)
    ensures Distinct(xs) <==> DistinctRecLast(xs)
  {
  }

  lemma DistinctSubseq<T>(xs: seq<T>, i: int, j: int)
    requires 0 <= i <= j <= |xs|
    requires Distinct(xs)
    ensures Distinct(xs[i..j])
  {
  }


  lemma DistinctImpDistinctReverse<T>(xs: seq<T>)
    ensures Distinct(xs) ==> Distinct(Reverse(xs))
  {
    ReverseIndexAll(xs);
  }

  lemma DistinctReverse<T>(xs: seq<T>)
    ensures Distinct(Reverse(xs)) <==> Distinct(xs)
  {
    if (Distinct(Reverse(xs))) {
      calc {
        Distinct(Reverse(xs));
        { DistinctImpDistinctReverse(Reverse(xs)); }
        Distinct(Reverse(Reverse(xs)));
        { ReverseReverse(xs); }
        Distinct(xs);
      }
    } else {
      DistinctImpDistinctReverse(xs);
    }
  }

  lemma DistinctAll<T>(xs: seq<T>)
    ensures Distinct(xs) <==> forall i, j :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j]
  {
  }

  lemma SortedStrictImpDistinct(xs: seq<int>)
    requires SortedStrict(xs)
    ensures Distinct(xs)
  {
  }

  /***** Palindrome *****/
  predicate palindrome?<T>(s : seq<T>) {
  if |s| <= 1 then true else (s[0] == s[|s|-1] && palindrome?(s[1..|s|-1]))
}

lemma palindromeOne<T>(s: seq<T>)
requires |s| == 1
ensures palindrome?(s)
{}

lemma palindromeIndex<T>(s: seq<T>)
requires palindrome?(s)
ensures forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1-i]
{}


lemma palindromToReverse<T>(s: seq<T>)
requires palindrome?(s)
ensures Reverse(s) == s
{
  palindromeIndex(s);
  ReverseIndexAll(s);
  //ReverseIndexAll(Reverse(s));
}

/*
lemma reverseToPalindrome<T>(s: seq<T>)
requires Reverse(s) == s
ensures palindrome?(s)
{
  ReverseIndexAll(s);
  ReverseIndexAll(Reverse(s));
}
*/

}