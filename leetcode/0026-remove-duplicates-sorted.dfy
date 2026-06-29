include "../lib/Seq.dfy"

import opened Seq

method RemveDuplicates(nums: array<int>) returns (length: int)
  modifies nums
  requires 1 <= nums.Length
  requires Sorted(nums[..])
  ensures 1 <= length <= nums.Length
  ensures SortedStrict(nums[..length])
  ensures Distinct(nums[..length])
  ensures forall x :: x in old(nums[..]) ==> x in nums[..length]
{
  var j := 0;
  var i := 1;
  while i < nums.Length
    invariant j < i <= nums.Length
    invariant nums[j + 1..] == old(nums[j + 1..])
    invariant SortedStrict(nums[..j + 1])
    invariant i < nums.Length ==> forall k :: 0 <= k < i ==> nums[k] <= nums[i]
    invariant forall k :: 0 <= k < i ==> old(nums[k]) in nums[..j + 1]
    invariant i < nums.Length ==> nums[j] <= nums[i]
  {
    if nums[i] != nums[j] {
      j := j + 1;
      nums[j] := nums[i];
      assert nums[..j + 1] == nums[..j] + [nums[i]];
    }
    i := i + 1;
  }
  return j + 1;
}