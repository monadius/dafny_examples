include "Seq.dfy"

module SeqMethods {
  import opened Seq

  method ReverseIter<T>(xs: seq<T>) returns (rev: seq<T>)
    ensures rev == Reverse(xs)
  {
    rev := [];
    var i := |xs|;
    while i > 0
      invariant i >= 0
      invariant rev == Reverse(xs[i..])
    {
      i := i - 1;
      rev := rev + [xs[i]];
    }
  }

  method ReverseArray<T>(a: array<T>) returns (rev: array<T>)
    ensures rev[..] == Reverse(a[..])
  {
    rev := new T[a.Length](i requires 0 <= i < a.Length reads a => a[a.Length - i - 1]);
    ReverseIndexAll(a[..]);
  }

  method ReverseArrayInPlace<T>(a: array<T>) returns (rev: array<T>)
    modifies a
    ensures rev == a
    ensures rev[..] == Reverse(old(a[..]))
  {
    var i := 0;
    var j := a.Length - 1;
    while i < j
      invariant 0 <= i <= a.Length
      invariant j < a.Length
      invariant j == a.Length - i - 1
      invariant forall k :: 0 <= k < i ==> a[k] == old(a[a.Length - k - 1])
      invariant forall k :: j < k < a.Length ==> a[k] == old(a[a.Length - k - 1])
      invariant forall k :: 0 <= i <= k <= j ==> a[k] == old(a[k])
    {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
      j := j - 1;
    }
    ReverseIndexAll(old(a[..]));
    return a;
  }

  method FoldlIter<A, B>(f: (A, B) -> A, z: A, xs: seq<B>) returns (r: A) 
    ensures r == Foldl'(f, z, xs)
    ensures r == Foldl(f, z, xs)
  {
    r := z;
    var i := 0;
    while i < |xs|
      invariant i <= |xs|
      invariant r == Foldl'(f, z, xs[..i])
    {
      r := f(r, xs[i]);
      i := i + 1;
      assert xs[..i] == xs[..i - 1] + [xs[i - 1]];
    }
    assert xs[..i] == xs;
    FoldlEq(f, z, xs);
  }

  method SumIter(xs: seq<int>) returns (s: int)
    ensures s == Sum(xs)
  {
    var i := 0;
    s := 0;
    while i < |xs|
      invariant i <= |xs|
      invariant s == Sum(xs[..i])
    {
      s := s + xs[i];
      i := i + 1;
      assert xs[..i] == xs[..i - 1] + [xs[i - 1]];
    }
    assert xs[..i] == xs;
  }

  method CheckDistinct<T(==)>(xs: seq<T>) returns (r: bool)
    ensures r <==> Distinct(xs)
  {
    var i := 0;
    var s: set<T> := {};
    while i < |xs|
      invariant i <= |xs|
      invariant forall x :: x in xs[..i] <==> x in s
      invariant Distinct(xs[..i])
    {
      if xs[i] in s {
        return false;
      }
      s := s + {xs[i]};
      i := i + 1;
    }
    return true;
  }

  method CheckDistinctSubseq<T(==)>(xs: seq<T>, start: int, end: int) returns (r: bool)
    requires 0 <= start <= end <= |xs|
    ensures r <==> Distinct(xs[start..end])
  {
    var i := start;
    var s: set<T> := {};
    while i < end
      invariant start <= i <= end
      invariant forall x :: x in xs[start..i] <==> x in s
      invariant Distinct(xs[start..i])
    {
      if xs[i] in s {
        return false;
      }
      s := s + {xs[i]};
      i := i + 1;
      assert xs[start..i] == xs[start..i - 1] + [xs[i - 1]];
    }
    return true;
  }

  method CheckDistinctSubarray<T(==)>(a: array<T>, start: int, end: int) returns (r: bool)
    requires 0 <= start <= end <= a.Length
    ensures r <==> Distinct(a[start..end])
  {
    var i := start;
    var s: set<T> := {};
    while i < end
      invariant start <= i <= end
      invariant forall x :: x in a[start..i] <==> x in s
      invariant Distinct(a[start..i])
    {
      if a[i] in s {
        return false;
      }
      s := s + {a[i]};
      i := i + 1;
    }
    return true;
  }

}