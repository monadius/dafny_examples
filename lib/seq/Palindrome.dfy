// Author: Shaobo He

include "../Seq.dfy"

import opened Seq

/***** Palindrome *****/
predicate Palindrome?<T(==)>(s: seq<T>) {
  if |s| <= 1 then true else (s[0] == s[|s|-1] && Palindrome?(s[1..|s|-1]))
}

lemma OneCharStringIsPalindrome<T>(s: seq<T>)
  ensures |s| == 1 ==> Palindrome?(s)
{}

lemma PalindromeIndex<T>(s: seq<T>)
  requires Palindrome?(s)
  ensures forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1-i]
{
  if |s| <= 1 {

  }
}

lemma PalindromeIndexRev<T>(s: seq<T>)
  requires forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1-i]
  ensures Palindrome?(s)
{}

lemma PalindromImpliesReverseEq<T>(s: seq<T>)
  requires Palindrome?(s)
  ensures Reverse(s) == s
{
  ReverseIndexAll(s);
  PalindromeIndex(s);
}

lemma ReverseEqImpliesPalindrom<T>(s: seq<T>)
  requires Reverse(s) == s
  ensures Palindrome?(s)
{
  ReverseIndexAll(s);
  PalindromeIndexRev(s);
}