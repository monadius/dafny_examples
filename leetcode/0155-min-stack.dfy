// include "../lib/Seq.dfy"

// import opened Seq

predicate IsMin(m: int, xs: seq<int>) {
  m in xs && forall i :: 0 <= i < |xs| ==> m <= xs[i]
}

class MinStack {
  var data: seq<int>
  var mins: seq<int>

  predicate Valid() 
    reads this
  {
    |mins| == |data|
    && (forall k :: 0 <= k < |mins| ==> IsMin(mins[k], data[k..]))
    // && (forall k :: 0 <= k < |mins| ==> mins[k] in data[k..])
  }

  constructor()
    ensures Valid()
  {
    data := [];
    mins := [];
  }

  method Push(val: int)
    modifies this
    requires Valid()
    ensures Valid()
  {
    data := [val] + data;
    mins := [if |mins| == 0 || val <= mins[0] then val else mins[0]] + mins;
    assert mins[1..] == old(mins);
  }

  method Pop() returns (val: int)
    modifies this
    requires Valid()
    requires |data| > 0
    ensures Valid()
  {
    val := data[0];
    data := data[1..];
    mins := mins[1..];
  }

  method Top() returns (val: int) 
    requires |data| > 0
    ensures val == data[0]
  {
    return data[0];
  }

  method GetMin() returns (min: int)
    requires Valid()
    requires |data| > 0
    ensures IsMin(min, data)
  {
    return mins[0];
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