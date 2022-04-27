include "../lib/Seq.dfy"
// include "../lib/WorkCount.dfy"

import opened Seq

function Count<T>(xs: seq<T>, v: T): int {
  Foldl'((r, x)=> r + (if x == v then 1 else 0), 0, xs)
}

// TODO: ensure that multiplicities of elements are preserved
method RemoveElement(nums: array<int>, val: int) returns (length: nat)
  modifies nums
  ensures length <= nums.Length
  ensures length == nums.Length - Count(old(nums[..]), val)
  ensures forall k :: 0 <= k < length ==> nums[k] != val
  ensures forall x :: x != val && x in old(nums[..]) ==> x in nums[..length]
  // ensures forall x :: x != val ==> Count(x, nums[..length]) == Count(x, old(nums[..]))
{
  var j, i := 0, 0;
  while i < nums.Length
    invariant 0 <= j <= i <= nums.Length
    invariant forall k :: 0 <= k < j ==> nums[k] != val
    invariant j == i - Count(old(nums[..i]), val)
    invariant old(nums[i..]) == nums[i..]
    invariant forall k :: 0 <= k < i ==> (old(nums[k]) != val <==> old(nums[k]) in nums[..j])
    invariant forall k :: 0 <= k < i && old(nums[k]) != val ==> Count(nums[..j], old(nums[k])) == Count(old(nums[..i]), old(nums[k]))
  {
    if nums[i] != val {
      nums[j] := nums[i];
      assert nums[..j + 1] == nums[..j] + [nums[i]];
      assert old(nums[..i + 1]) == old(nums[..i]) + [nums[i]];
      assert Count(nums[..j + 1], nums[i]) == 1 + Count(nums[..j], nums[i]);
      assert Count(old(nums[..i + 1]), nums[i]) == 1 + Count(old(nums[..i]), nums[i]);
      
      assert Count(nums[..j + 1], nums[i]) == Count(old(nums[..i + 1]), nums[i]) by {
        if exists k :: 0 <= k < i && old(nums[k]) == nums[i] {
          // ghost var k :| 0 <= k < i && old(nums[k]) == nums[i];
          // assume false;
        } else {
          assert nums[i] !in nums[..j];
          // assume false;
        }
        // calc {
        //   Count(nums[..j + 1], nums[i]);
        //   1 + Count(nums[..j], nums[i]);
        // }
      }
      j := j + 1;
      // assume false;
    }
    assert old(nums[i + 1..]) == nums[i + 1..];
    assert old(nums[..i + 1]) == old(nums[..i]) + old([nums[i]]);
    i := i + 1;
  }
  assert old(nums[..i]) == old(nums[..]);
  return j;
}

// method RemoveElement2(nums: array<int>, val: int) returns (length: nat)
//   modifies nums
//   ensures length <= nums.Length
//   ensures forall k :: 0 <= k < length ==> nums[k] != val
//   // ensures forall x :: x != val && x in old(nums[..]) ==> x in nums[..length]
// {
//   var j, i := nums.Length, 0;
//   while i < j
//     invariant 0 <= i <= j <= nums.Length
//     invariant forall k :: 0 <= k < i ==> nums[k] != val
//     invariant old(nums[j..]) == nums[j..]
//     // invariant forall k :: 0 <= k < i && old(nums[k]) != val ==> old(nums[k]) in nums[..i]
//   {
//     if nums[i] == val {
//       assert old(nums[j..]) == nums[j..];
//       assert nums[j - 1..] == [nums[j - 1]] + nums[j..];
//       if j == i + 1 {
//         assume false;
//       } else {
//         assume false;
//       }
//       j := j - 1;
//       nums[i] := nums[j];
//     } else {
//       // assert nums[..i + 1] == nums[..i] + [nums[i]];
//       // assert old(nums[i]) == nums[i];
//       i := i + 1;
//     }
//   }
//   return j;
// }