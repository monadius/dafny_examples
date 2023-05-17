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
}

lemma PalindromIndexImp<T>(s: seq<T>)
ensures Palindrome?(s) ==> (forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1-i])
{
  if Palindrome?(s) {
    PalindromeIndex(s);
  }
}

lemma PalindromRelReverse<T>(s: seq<T>)
ensures Palindrome?(s) <==> Reverse(s) == s
{
  if |s| > 1 {
    var t := s[1..|s| - 1];
    ReverseIndexAll(s);
    ReverseIndexAll(t);
  }
}