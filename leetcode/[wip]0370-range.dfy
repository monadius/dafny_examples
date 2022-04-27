include "../lib/Seq.dfy"

import opened Seq

function AddRange(xs: seq<int>, a: int, b: int, v: int): seq<int> {
  seq(|xs|, i requires 0 <= i < |xs| => xs[i] + if a <= i <= b then v else 0)
}

function PerformUpdates(xs: seq<int>, updates: seq<(int, int, int)>): seq<int> 
  decreases updates
{
  if |updates| == 0 then
    xs
  else
    var (a, b, v) := updates[0];
    PerformUpdates(AddRange(xs, a, b, v), updates[1..])
}

lemma PerformUpdates1(xs: seq<int>, u: seq<(int, int, int)>)
  requires |u| > 0
  ensures PerformUpdates(xs, u) == PerformUpdates(PerformUpdates(xs, u[..|u| - 1]), [u[|u| - 1]])
{

}

// method AddRangeTest(xs: array<int>, a: int, b: int, v: int) returns (ys: array<int>)
//   requires 0 <= a <= b < xs.Length
//   ensures ys[..] == AddRange(xs[..], a, b, v)
// {
//   ys := new int[xs.Length];
//   forall i | 0 <= i < xs.Length {
//     ys[i] := xs[i];
//   }
//   assert ys[..] == xs[..];
//   var i := a;
//   while i <= b
//     invariant 0 <= i <= xs.Length
//     invariant ys[i..] == xs[i..]
//     invariant ys[..i] == AddRange(xs[..i], a, b, v)
//   {
//     ys[i] := ys[i] + v;
//     i := i + 1;
//   }
// }

method GetModifiedArraySimple(length: int, updates: array<(int, int, int)>) returns (arr: array<int>)
  requires 1 <= length
  requires forall k :: 0 <= k < updates.Length ==> 0 <= updates[k].0 <= updates[k].1 < length
  ensures arr.Length == length
  ensures arr[..] == PerformUpdates(seq(length, _ => 0), updates[..])
{
  arr := new int[length](_ => 0);
  ghost var s := seq(length, _ => 0);
  assert arr[..] == s;
  var k := 0;
  while k < updates.Length
    invariant 0 <= k <= updates.Length
    invariant arr[..] == s
    invariant s == PerformUpdates(seq(length, _ => 0), updates[..k])
  {
    var (a, b, v) := updates[k];
    ghost var vs := arr[..];
    ghost var us := updates[..k];
    s := AddRange(s, a, b, v);
    assert vs == PerformUpdates(seq(length, _ => 0), us);
    var i := a;
    while i <= b
      invariant i <= b + 1
      invariant arr[i..] == vs[i..];
      invariant s[..i] == arr[..i]
      invariant s[b + 1..] == arr[b + 1..]
      invariant vs == PerformUpdates(seq(length, _ => 0), us)
      invariant updates[..k] == us
    {
      arr[i] := arr[i] + v;
      i := i + 1;
    }
    assert vs == PerformUpdates(seq(length, _ => 0), us);
    assert s == PerformUpdates(vs, [updates[k]]);
    PerformUpdates1(seq(length, _ => 0), updates[..k + 1]);
    k := k + 1;
    // assume s == PerformUpdates(seq(length, _ => 0), updates[..k]);
  }
  assert updates[..] == updates[..updates.Length];
}