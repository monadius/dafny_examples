include "../Seq.dfy"

import opened Seq

predicate {:opaque} Subseq<T(==)>(xs: seq<T>, ys: seq<T>) {
  if |xs| == 0 then true
  else if |ys| == 0 then false
  else if xs[0] == ys[0] then Subseq(xs[1..], ys[1..])
  else Subseq(xs, ys[1..])
}

lemma SubseqRefl<T>(xs: seq<T>)
  ensures Subseq(xs, xs)
{
  reveal Subseq();
}

lemma SubseqTail<T>(xs: seq<T>, ys: seq<T>)
  requires 0 < |xs|
  requires Subseq(xs, ys)
  ensures Subseq(xs[1..], ys)
{
  reveal Subseq();
}

lemma SubseqTrans<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
  requires Subseq(xs, ys) && Subseq(ys, zs)
  ensures Subseq(xs, zs)
{
  reveal Subseq();
  if |xs| == 0 {
  } else {
    if |ys| > 0 {
      if xs[0] != ys[0] {
        assert Subseq(xs, ys[1..]);
        SubseqTail(ys, zs);
        SubseqTrans(xs, ys[1..], zs);
      }
    }
  }
}

lemma LengthSubseq<T>(xs: seq<T>, ys: seq<T>)
  requires Subseq(xs, ys)
  ensures |xs| <= |ys|
{
  reveal Subseq();
}

lemma MemSubseq<T>(xs: seq<T>, ys: seq<T>, x: T)
  requires Subseq(xs, ys)
  ensures x in xs ==> x in ys
{
  reveal Subseq();
}

lemma SubseqSlice<T>(xs: seq<T>, i: int, j: int)
  requires 0 <= i <= j <= |xs|
  ensures Subseq(xs[i..j], xs)
{
  reveal Subseq();
  if |xs| == 0 || i == j {
  } else if i < |xs| {
    if 0 < i {
      if xs[i] == xs[0] {
        SubseqSlice(xs[1..], i, j - 1);
        assert xs[i + 1..j] == xs[1..][i..j - 1];
      } else {
        SubseqSlice(xs[1..], i - 1, j - 1);
        assert xs[i..j] == xs[1..][i - 1..j - 1];
      }
    } else {
      SubseqSlice(xs[1..], 0, j - 1);
      assert xs[1..j] == xs[1..][0..j - 1];
    }
  }
}

lemma SubseqRemoveLast<T>(xs: seq<T>)
  requires 0 < |xs|
  ensures Subseq(RemoveLast(xs), xs)
{
  SubseqSlice(xs, 0, |xs| - 1);
}

// lemma SubseqConcat<T>(xs1: seq<T>, ys1: seq<T>, xs2: seq<T>, ys2: seq<T>)
//   requires Subseq(xs1, ys1) && Subseq(xs2, ys2)
//   ensures Subseq(xs1 + xs2, ys1 + ys2)
// {
//   reveal Subseq();
  
// }
