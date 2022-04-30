include "../Seq.dfy"

import opened Seq

function {:opaque} Undup<T>(xs: seq<T>): seq<T> {
  if |xs| == 0 then xs 
  else if Last(xs) in RemoveLast(xs) then Undup(RemoveLast(xs))
  else Undup(RemoveLast(xs)) + [Last(xs)]
}

lemma MemUndup<T>(xs: seq<T>)
  ensures forall x :: x in Undup(xs) <==> x in xs
{
  reveal Undup();
}

lemma DistinctUndup<T>(xs: seq<T>)
  ensures Distinct(Undup(xs))
{
  reveal Undup();
  if |xs| != 0 && Last(xs) !in RemoveLast(xs) {
    MemUndup(RemoveLast(xs));
  }
}

// lemma SubseqUndup<T>(xs: seq<T>)
//   ensures Subseq(Undup(xs), xs)
// {
//   reveal Subseq();
//   reveal Undup();
//   if |xs| == 0 {
//   } else if Last(xs) in RemoveLast(xs) {
//     SubseqRemoveLast(xs);
//     SubseqTrans(Undup(xs), RemoveLast(xs), xs);
//   } else {

//     // SubseqRemoveLast(xs);
//     // assume false;
//   }
// }