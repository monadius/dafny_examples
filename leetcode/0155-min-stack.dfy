// include "../lib/Seq.dfy"

// import opened Seq

include "../lib/List.dfy"

import opened ListModule

predicate IsMin(m: int, xs: seq<int>) {
  m in xs && forall i :: 0 <= i < |xs| ==> m <= xs[i]
}

class MinStack {
  var data : List<int>
  var mins : List<int>

  ghost var dataSeq: seq<int>
  ghost var minsSeq: seq<int>

  ghost predicate Valid() 
    reads this
  {
    ToSeq(data) == dataSeq && ToSeq(mins) == minsSeq && |dataSeq| == |minsSeq|
    && (forall k :: 0 <= k < |minsSeq| ==> IsMin(minsSeq[k], dataSeq[k..]))
  }

  constructor()
    ensures Valid()
  {
    data := Nil;
    mins := Nil;
    dataSeq := [];
    minsSeq := [];
  }

  predicate IsEmpty()
    reads this
    requires Valid()
    ensures IsEmpty() <==> |dataSeq| == 0
  {
    data.Nil?
  }

  method Push(val: int)
    modifies this
    requires Valid()
    ensures dataSeq == [val] + old(dataSeq)
    ensures Valid()
    ensures !IsEmpty()
  {
    var min := if mins.Nil? || val <= mins.head then val else mins.head;
    data := Cons(val, data);
    mins := Cons(min, mins);
    dataSeq := [val] + dataSeq;
    minsSeq := [min] + minsSeq;

    // assert minsSeq[1..] == old(minsSeq);
    assert dataSeq[1..] == old(dataSeq);
  }

  method Pop() returns (val: int)
    modifies this
    requires Valid()
    requires !IsEmpty()
    ensures dataSeq == old(dataSeq[1..])
    ensures Valid()
  {
    val := data.head;
    data := data.tail;
    mins := mins.tail;
    dataSeq := dataSeq[1..];
    minsSeq := minsSeq[1..];
  }

  method Top() returns (val: int)
    requires Valid()
    requires !IsEmpty()
    ensures val == dataSeq[0]
  {
    return data.head;
  }

  method GetMin() returns (min: int)
    requires Valid()
    requires !IsEmpty()
    ensures IsMin(min, dataSeq)
  {
    assert mins.head == minsSeq[0];
    return mins.head;
  }
}

// class MinStackLessMemory {
//   var data: seq<int>
//   var mins: seq<int>
//   ghost var minIndices: seq<int>

//   predicate Valid() 
//     reads this
//   {
//     |mins| == |minIndices|
//     && |mins| <= |data|
//     && (|data| > 0 ==> |mins| > 0)
//     && (forall k :: 0 <= k < |minIndices| ==> 0 <= minIndices[k] <= |data|)
//     && (forall k :: 0 <= k < |minIndices| ==> IsMin(mins[k], data[..minIndices[k]]))
//     && (|mins| > 0 ==> forall i :: Last(minIndices) <= i < |data| ==> Last(mins) < data[i])
//   }

//   constructor()
//     ensures Valid()
//   {
//     data := [];
//     mins := [];
//     minIndices := [];
//   }

//   method Push(val: int)
//     modifies this
//     requires Valid()
//     ensures Valid()
//   {
//     data := data + [val];
//     if |mins| == 0 || val <= Last(mins) {
//       mins := mins + [val];
//       minIndices := minIndices + [|data|];
//       assume IsMin(Last(mins), data[..Last(minIndices)]);
//       assert data == data[..Last(minIndices)];
//     }
//   }

//   method Pop() returns (val: int)
//     modifies this
//     requires Valid()
//     requires |data| > 0
//     ensures Valid()
//   {
//     val := data[0];
//     data := data[1..];
//     if mins[0] == val {
//       mins := mins[1..];
//       minIndices := minIndices[1..];
//     }
//   }

//   method Top() returns (val: int) 
//     requires |data| > 0
//   {
//     return Last(data);
//   }

//   method GetMin() returns (min: int)
//     requires Valid()
//     requires |data| > 0
//     ensures IsMin(min, data)
//   {
//     return Last(mins);
//   }
// }