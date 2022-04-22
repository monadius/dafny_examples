include "../lib/MinMax.dfy"
include "../lib/Seq.dfy"
include "../lib/SeqMethods.dfy"

import opened MinMax
import opened Seq
import opened SeqMethods

method LengthOfLongestSubstringSimple(s: string) returns (maxLength: int)
  ensures forall u, v :: 0 <= u <= v <= |s| && Distinct(s[u..v]) ==> v - u <= maxLength
  ensures exists u, v :: 0 <= u <= v <= |s| && v - u == maxLength && Distinct(s[u..v])
{
  maxLength := 0;
  ghost var u, v := 0, 0;
  var i := 0;
  while i < |s|
    invariant i <= |s|
    invariant 0 <= maxLength
    invariant forall u, v :: 0 <= u < i && u <= v <= |s| && Distinct(s[u..v]) ==> v - u <= maxLength
    invariant 0 <= u <= v <= |s| && v - u == maxLength && Distinct(s[u..v])
  {
    var j := i + 1;
    while j <= |s|
      invariant i < j <= |s| + 1
      invariant 0 <= maxLength
      invariant forall v :: i <= v < j && Distinct(s[i..v]) ==> v - i <= maxLength
      invariant forall u, v :: 0 <= u < i && u <= v <= |s| && Distinct(s[u..v]) ==> v - u <= maxLength
      invariant 0 <= u <= v <= |s| && v - u == maxLength && Distinct(s[u..v])
    {
      var r := CheckDistinctSubseq(s, i, j);
      if r {
        if j - i > maxLength {
          v := j;
          u := i;
        }
        maxLength := Max(maxLength, j - i);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method LengthOfLongestSubstring(s: string) returns (maxLength: int)
  ensures forall u, v :: 0 <= u <= v <= |s| && Distinct(s[u..v]) ==> v - u <= maxLength
  ensures exists u, v :: 0 <= u <= v <= |s| && v - u == maxLength && Distinct(s[u..v])
{
  maxLength := 0;
  var ind: map<char, int> := map[];
  ghost var u, v := 0, 0;
  var left := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= maxLength
    invariant i <= |s|
    invariant forall k :: k in ind ==> 0 <= ind[k] < i
    invariant forall k :: k in ind ==> s[ind[k]] == k
    invariant forall k :: k in ind ==> k !in s[ind[k] + 1..i]
    invariant forall k :: k !in ind ==> k !in s[..i]
    invariant 0 <= left <= i
    invariant Distinct(s[left..i])
    invariant forall u :: 0 <= u <= i && Distinct(s[u..i]) ==> left <= u
    invariant forall u, v :: 0 <= u <= v <= i && Distinct(s[u..v]) ==> v - u <= maxLength
    invariant 0 <= u <= v <= i && v - u == maxLength && Distinct(s[u..v])
  {
    if s[i] in ind {
      left := Max(left, ind[s[i]] + 1);
    }
    ghost var oldInd := ind;
    ind := ind[s[i] := i];
    if i - left + 1 > maxLength {
      u, v := left, i + 1;
    }
    maxLength := Max(maxLength, i - left + 1);
    assert Distinct(s[left..i + 1]) by {
      assert s[left..i + 1] == s[left..i] + [s[i]];
    }
    i := i + 1;
    forall u | 0 <= u <= i && Distinct(s[u..i]) ensures left <= u {
      if (u < i) {
        assert Distinct(s[u..i - 1]) by {
          assert s[u..i - 1] == RemoveLast(s[u..i]);
        }
        if s[i - 1] in oldInd {
          if u <= oldInd[s[i - 1]] {
          }
        }
      }
    }
  }
}