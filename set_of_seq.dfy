function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s
}

lemma in_set_of_seq<T>(x: T, s: seq<T>)
  ensures x in set_of_seq(s) <==> x in s
{
}

lemma subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
  requires set_of_seq(s1) <= set_of_seq(s2)
  ensures forall x :: x in s1 ==> x in s2
{
  forall x | x in s1 {
    in_set_of_seq(x, s1);
  }
}

lemma set_of_seq_subset<T>(s1: seq<T>, s2: seq<T>)
  requires forall x :: x in s1 ==> x in s2
  ensures set_of_seq(s1) <= set_of_seq(s2)
{
}

function set_of_seq_ind<T>(s: seq<T>): set<T>
{
  if s == [] then {} else {s[0]} + set_of_seq_ind(s[1..])
}

lemma set_of_seq_ind_eq<T>(s: seq<T>)
  ensures set_of_seq(s) == set_of_seq_ind(s)
{
  if s == [] {

  } else {
    assert (set x: T | x in s[1..]) == set_of_seq_ind(s[1..]);
    assert (set x: T | x in s) == ({s[0]} + (set x: T | x in s[1..]));
  }
}

lemma card_set_of_seq_le<T>(s: seq<T>)
  ensures |set_of_seq(s)| <= |s|
{
  if s == [] {
  }
  else {
    calc {
      |set_of_seq(s)|;
      == { set_of_seq_ind_eq(s); }
        |set_of_seq_ind(s)|;
      == { assert s == [s[0]] + s[1..]; }
        |set_of_seq_ind([s[0]] + s[1..])|;
      <= 1 + |set_of_seq_ind(s[1..])|;
      == { set_of_seq_ind_eq(s[1..]); }
        1 + |set_of_seq(s[1..])|;
      <= { card_set_of_seq_le(s[1..]); }
        1 + |s[1..]|;
    }
  }
}

lemma set_of_seq_append<T>(s1: seq<T>, s2: seq<T>)
  ensures set_of_seq(s1 + s2) == set_of_seq(s1) + set_of_seq(s2)
{
}

function undup<T(==)>(s: seq<T>): seq<T>
{
  if s == [] then
    []
  else if s[0] in s[1..] then
    undup(s[1..])
  else
    [s[0]] + undup(s[1..])
}

lemma in_undup<T>(x: T, s: seq<T>)
  ensures x in undup(s) <==> x in s
{
}

lemma set_of_seq_undup<T>(s: seq<T>)
  ensures set_of_seq(undup(s)) == set_of_seq(s)
{
  if s == [] {
  }
  else {
//    set_of_seq_ind_eq(undup(s));
//    assert s == [s[0]] + s[1..];
//    set_of_seq_ind_eq(undup(s[1..]));
    calc {
      set_of_seq(undup(s));
      { set_of_seq_ind_eq(undup(s)); }
      set_of_seq_ind(undup(s));
      { assert s == [s[0]] + s[1..]; set_of_seq_ind_eq(undup(s[1..])); }
      if s[0] in s[1..] then set_of_seq(undup(s[1..])) else {s[0]} + set_of_seq(undup(s[1..]));
    }
  }
}

lemma undup_undup<T>(s: seq<T>)
  ensures undup(undup(s)) == undup(s)
{
  if s == [] {
  }
  else if s[0] in s[1..] {  
//    assert s == [s[0]] + s[1..];
//    set_of_seq_ind_eq(s);
//    set_of_seq_ind_eq(s[1..]);
  }
  else {
//    assume undup(s[1..]) == undup(s)[1..];
    in_undup(s[0], s[1..]);
//    assert s[0] !in undup(s[1..]);
  }
}

predicate subseq<T(==)>(s1: seq<T>, s2: seq<T>)
{
  if s1 == [] then
    true
  else if s2 == [] then
    false
  else if s1[0] == s2[0] then
    subseq(s1[1..], s2[1..])
  else
    subseq(s1, s2[1..])
}

lemma subseq_length<T>(s1: seq<T>, s2: seq<T>)
  requires subseq(s1, s2)
  ensures |s1| <= |s2|
{
}

lemma set_of_subseq<T>(s1: seq<T>, s2: seq<T>)
  requires subseq(s1, s2)
  ensures set_of_seq(s1) <= set_of_seq(s2)
{
  if s1 == [] {
  }
  else {
    set_of_seq_ind_eq(s1);
    set_of_seq_ind_eq(s2);
    set_of_seq_ind_eq(s1[1..]);
    set_of_seq_ind_eq(s2[1..]);
    assert s1 == [s1[0]] + s1[1..];
    assert s2 == [s2[0]] + s2[1..];
  }
}

lemma subseq_refl<T>(s: seq<T>)
  ensures subseq(s, s)
{
}

lemma in_subseq<T>(x: T, s1: seq<T>, s2: seq<T>)
  requires subseq(s1, s2)
  ensures x in s1 ==> x in s2
{
}

predicate uniq_ind<T(==)>(s: seq<T>)
{
  if s == [] then
    true
  else if s[0] in s[1..] then
    false
  else
    uniq_ind(s[1..])
}

lemma undup_uniq<T>(s: seq<T>)
  requires uniq_ind(s)
  ensures undup(s) == s
{
}

lemma uniq_undup<T>(s: seq<T>)
  ensures uniq_ind(undup(s))
{
  if s == [] {
  }
  else {
    in_undup(s[0], s[1..]);
  }
}

/*
lemma card_set_of_undup<T>(s: seq<T>)
  ensures |set_of_seq_ind(undup(s))| == |undup(s)|
{
  if s == [] {
  }
  else if s[0] in s[1..] {
  }
  else {
//    in_undup(s[0], s[1..]);
//    assert s[0] !in undup(s[1..]);
    calc {
      |set_of_seq_ind(undup(s))|;
      |set_of_seq_ind([s[0]] + undup(s[1..]))|;
      |{s[0]} + set_of_seq_ind(undup(s[1..]))|;
      { set_of_seq_ind_eq(undup(s[1..]));
        in_undup(s[0], s[1..]);
        assert s[0] !in set_of_seq_ind(undup(s[1..])); }
      1 + |set_of_seq_ind(undup(s[1..]))|;
    }
  }
}
*/

lemma card_set_of_seq_uniq<T>(s: seq<T>)
  requires uniq_ind(s)
  ensures |set_of_seq(s)| == |s|
{
  if s == [] {
  }
  else if s[0] in s[1..] {
  }
  else {
    set_of_seq_ind_eq(s[1..]);
    set_of_seq_ind_eq(s);
  }
    
//  undup_uniq(s);
//  set_of_seq_ind_eq(s);
//  card_set_of_undup(s);
}

lemma card_set_of_undup<T>(s: seq<T>)
  ensures |set_of_seq(undup(s))| == |undup(s)|
{
  uniq_undup(s);
  card_set_of_seq_uniq(undup(s));
}
