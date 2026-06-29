// Author: Shaobo He
include "../lib/MinMax.dfy"
include "../lib/Seq.dfy"

import opened MinMax
import opened Seq

lemma SumInd(nums: seq<int>, i : nat)
requires 0 <= i <= |nums|
ensures forall j :: 0 <= j < i ==> Sum(nums[j..i]) == Sum(nums[j..i-1]) + nums[i-1]
{
    assert forall j :: 0 <= j < i ==> nums[j..i] == nums[j..i-1] + [nums[i-1]];
}

method maxSubArray(nums: seq<int>) returns(r: int)
requires |nums| >= 1
ensures forall i, j {:trigger nums[i..j+1]} :: 0 <= i <= j < |nums| ==> Sum(nums[i..j+1]) <= r
ensures exists i, j {:trigger nums[i..j+1]} :: 0 <= i <= j < |nums| && Sum(nums[i..j+1]) == r
{
    var curr_max := nums[0];
    r := nums[0];

    SumConcat(nums[0..1], []);
    var i := 1;
    while i < |nums|
    decreases |nums| - i
    invariant 1 <= i <= |nums|
    invariant forall j {:trigger nums[j..i]} :: 0 <= j < i ==> Sum(nums[j..i]) <= curr_max
    invariant exists j {:trigger nums[j..i]} :: 0 <= j < i && Sum(nums[j..i]) == curr_max
    invariant forall p, q {:trigger nums[p..q+1]} :: 0 <= p <= q < i ==> Sum(nums[p..q+1]) <= r
    invariant exists p, q {:trigger nums[p..q+1]} :: 0 <= p <= q < i && Sum(nums[p..q+1]) == r
    {
        curr_max := Max(nums[i], curr_max+nums[i]);
        assert forall j :: 0 <= j <= i ==> nums[j..i+1] == nums[j..i] + [nums[i]];
        r := Max(r, curr_max);
        i := i + 1;
        SumInd(nums, i);
    }
}
