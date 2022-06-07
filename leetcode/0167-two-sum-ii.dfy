// Author: Shaobo He
include "../lib/Seq.dfy"

import opened Seq

function method TwoSumF(numbers: seq<int>, target: int, left: int, right: int) : (int, int)
requires 0 <= left <= right < |numbers|;
requires Sorted(numbers);
decreases right - left;
{
    if left == right
    then (-1, -1)
    else if numbers[left] + numbers[right] == target
    then (left, right)
    else if numbers[left] + numbers[right] > target
    then TwoSumF(numbers, target, left, right - 1)
    else TwoSumF(numbers, target, left + 1, right)

}

lemma CaseFound(numbers: seq<int>, target: int, left: int, right: int)
requires Sorted(numbers)
requires 0 <= left <= right < |numbers|
decreases right - left
ensures TwoSumF(numbers, target, left, right).0 >= 0 ==>
    0 <= TwoSumF(numbers, target, left, right).0 < TwoSumF(numbers, target, left, right).1 < |numbers| &&
    numbers[TwoSumF(numbers, target, left, right).0] + numbers[TwoSumF(numbers, target, left, right).1] == target
{}

lemma CaseNotFound(numbers: seq<int>, target: int, left: int, right: int)
requires Sorted(numbers)
requires 0 <= left <= right < |numbers|
decreases right - left
ensures TwoSumF(numbers, target, left, right).0 == -1 ==>
    forall i, j :: left <= i < j <= right ==> numbers[i] + numbers[j] != target
{
    if left == right {
        // pass
    } else if numbers[left] + numbers[right] == target {
        // pass
    } else if numbers[left] + numbers[right] > target {
        CaseNotFound(numbers, target, left, right - 1);
    } else {
        CaseNotFound(numbers, target, left+1, right);
    }
}

// Note that the return indices start with 0 instead of 1, to be consistent
// with other questions.
method TwoSum(numbers: seq<int>, target: int) returns (r: (int, int))
requires Sorted(numbers);
requires |numbers| >= 2;
ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < |numbers| && 
                       numbers[r.0] + numbers[r.1] == target;
ensures r.0 == -1 ==> forall i, j :: 0 <= i < j < |numbers| ==> numbers[i] + numbers[j] != target;
{
    /*
    var left, right := 0, |numbers|-1;
    while left < right
    invariant 0 <= left <= right < |numbers|;
    invariant forall i :: right < i < |numbers| ==> numbers[i] + numbers[left] > target;
    invariant forall i :: 0 <= i < left ==> numbers[i] + numbers[right] < target;
    {
        var sum := numbers[left] + numbers[right];
        if sum == target {
            return (left, right);
        } else if sum > target {
            right := right - 1;
        } else {
            left := left + 1;
        }
    }
    return (-1, -1);
    */

    r := TwoSumF(numbers, target, 0, |numbers|-1);
    CaseFound(numbers, target, 0, |numbers|-1);
    CaseNotFound(numbers, target, 0, |numbers|-1);
}