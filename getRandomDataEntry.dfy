method random(a: int, b: int) returns (r: int)
  ensures a <= b ==> a <= r <= b

method swap<T>(a: array<T>, i: int, j: int)
  // requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}

predicate uniq<T(==)>(s: seq<T>)
{
  forall x :: x in s ==> multiset(s)[x] == 1
}

lemma uniq_multiset_subset<T>(s1: seq<T>, s2: seq<T>)
  requires forall x :: x in s1 ==> x in s2
  requires uniq(s1)
  ensures multiset(s1) <= multiset(s2)
{
  forall x | x in s1 ensures multiset(s1)[x] <= multiset(s2)[x] {
//    calc {
//      1;
//      multiset(s1)[x];
//    }
  }
}

lemma card_multiset_subset<T>(m1: multiset<T>, m2: multiset<T>)
  requires m1 <= m2
  ensures |m1| <= |m2|
{
  if m1 == multiset{} {
  }
  else {
    var x :| x in m1;
//    assert x in m2;
//    assert |m1| == |m1 - multiset{x}| + 1;
//    assert |m2| == |m2 - multiset{x}| + 1;
//    assert m1 - multiset{x} <= m2 - multiset{x};
    card_multiset_subset(m1 - multiset{x}, m2 - multiset{x});
  }
}

lemma suffix_multiset_subset<T>(s: seq<T>, k: int)
  requires 0 <= k < |s|
  ensures multiset(s[k..]) <= multiset(s)
{
  assert s == s[..k] + s[k..];
}

method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  modifies m_workList
  requires m_workList.Length > 0
  requires uniq(m_workList[..])
  requires |avoidSet| < m_workList.Length
  ensures multiset(m_workList[..]) == old(multiset(m_workList[..]))
  ensures e in m_workList[..] && e !in avoidSet
{
  var k := m_workList.Length - 1;

  while (k >= 0)
    invariant k >= -1
    invariant forall x :: x in m_workList[(k + 1)..] ==> x in avoidSet
    invariant multiset(m_workList[..]) == old(multiset(m_workList[..]))
  {
    var i := random(0, k);
    assert i >= 0 && i <= k;

    e := m_workList[i];
    if (e !in avoidSet) {
      return e;
    }

    swap(m_workList, i, k);
    k := k - 1;
  }

  calc {
       m_workList.Length;
    == |multiset(m_workList[..])|;
    <= { uniq_multiset_subset(m_workList[..], avoidSet);
        card_multiset_subset(multiset(m_workList[..]), multiset(avoidSet)); }
       |multiset(avoidSet)|;
    == |avoidSet|; // a contradiction!
  }
//  assert forall x :: x in m_workList[..] ==> x in avoidSet;
//  assert uniq(m_workList[..]);
//  multiset_subset(m_workList[..], avoidSet);
//  assert multiset(m_workList[..]) <= multiset(avoidSet);
//  card_multiset_subset(multiset(m_workList[..]), multiset(avoidSet));
//  assert |multiset(m_workList[..])| <= |multiset(avoidSet)|;
//  assert false;
  
  return m_workList[0];
}

method fillWithRandomDataEntries<T(==, 0)>(m_workList: array<T>, n: int, avoidSet: seq<T>)
  returns (out: array<T>)
  modifies m_workList
  // requires m_workList != null
  requires uniq(m_workList[..])
  requires |avoidSet| + n <= m_workList.Length;
  requires n >= 0
  ensures multiset(m_workList[..]) == old(multiset(m_workList[..]))
  ensures out.Length == n;
  ensures forall x :: x in out[..] ==> x in m_workList[..] && x !in avoidSet
  ensures uniq(out[..])
{
  out := new T[n];

  var k := m_workList.Length - 1;
  var r := 0;
  
  while (k >= 0 && r < n)
    invariant k >= -1
    invariant r <= n
    invariant multiset(m_workList[..]) == old(multiset(m_workList[..]))
    invariant forall x :: x in m_workList[(k + 1)..] && x !in out[0..r] ==> x in avoidSet
    invariant forall x :: x in out[0..r] ==> x in m_workList[(k + 1)..] && x !in avoidSet
    invariant multiset(out[0..r]) <= multiset(m_workList[..])
  {
    var i := random(0, k);
    assert i >= 0 && i <= k;

    var e := m_workList[i];
    swap(m_workList, i, k);

    if (e in avoidSet) {
      // continue
    }
    else {
      out[r] := e;

      assert forall x :: x in out[0..r] ==> x in m_workList[(k + 1)..] && x !in avoidSet;
      // assert multiset(out[0..r]) <= multiset(m_workList[..]);

//      assert e == m_workList[k];
      suffix_multiset_subset(m_workList[..], k);
      assert multiset(m_workList[k..]) <= multiset(m_workList[..]);
//      assert uniq(m_workList[k..]);

      if e in out[0..r] {
        assert e in m_workList[(k + 1)..];
        calc {
          multiset(m_workList[k..])[e];
          { assert m_workList[k..] == m_workList[k..k+1] + m_workList[k+1..]; }
          multiset(m_workList[k..k+1] + m_workList[k+1..])[e];
          >= 2; // a contradiction!
        }
      }
//      assert e !in out[0..r];
      
      r := r + 1;
    }
    
    k := k - 1;
  }

  if r < n {
//    assert k == -1;
//    assert forall x :: x in m_workList[..] ==> x in avoidSet || x in out[0..r];
//    assert forall x :: x in m_workList[..] ==> x in avoidSet + out[0..r];

    uniq_multiset_subset(m_workList[..], avoidSet + out[0..r]);
    card_multiset_subset(multiset(m_workList[..]), multiset(avoidSet + out[0..r]));

//    assert false;
  }
  else {
//    assert r == n;
    assert out[0..n] == out[..];
  }

//  assert r == n;
}
