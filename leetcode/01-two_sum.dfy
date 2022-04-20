method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && nums[r.0] + nums[r.1] == target
  // ensures r.0 == -1 ==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m: map<int, int> := map[];
  var i := 0;
  while i < nums.Length
    invariant i <= nums.Length
    invariant forall k :: k in m ==> 0 <= m[k] < i
    invariant forall k :: k in m ==> nums[m[k]] + k == target
    // invariant forall u, v :: 0 <= u < v < i ==> nums[u] + nums[v] in s
    invariant forall j :: 0 <= j < i ==> target - nums[j] in m
    // invariant forall j :: 0 <= j < i ==> nums[j] !in m
    // invariant forall u, v :: 0 <= u < v < i ==> nums[u] + nums[v] != target
  {
    if nums[i] in m {
      return (m[nums[i]], i);
    }
    // assert forall j :: 0 <= j < i ==> nums[j] + nums[i] != target;
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  return (-1, -1);
}