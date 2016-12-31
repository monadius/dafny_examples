method random(a: int, b: int) returns (r: int)
	ensures a <= b ==> a <= r <= b

method swap<T>(a: array<T>, i: int, j: int)
	requires a != null
	requires 0 <= i < a.Length && 0 <= j < a.Length
	modifies a
	ensures a[i] == old(a[j])
	ensures a[j] == old(a[i])
	ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
	ensures multiset(a[..]) == old(multiset(a[..]))
{
	var t := a[i];
	a[i] := a[j];
	a[j] := t;
}

predicate uniq<T(==)>(s: seq<T>)
{
	forall x :: x in s ==> multiset(s)[x] == 1
}

lemma uniq_multiset_subset<T>(s1: seq<T>, s2: seq<T>)
	requires forall x :: x in s1 ==> x in s2
	requires uniq(s1)
	ensures multiset(s1) <= multiset(s2)
{
	forall x | x in s1 ensures multiset(s1)[x] <= multiset(s2)[x] {
	}
}

lemma card_multiset_subset<T>(m1: multiset<T>, m2: multiset<T>)
	requires m1 <= m2
	ensures |m1| <= |m2|
{
	if m1 == multiset{} {
	}
	else {
		var x :| x in m1;
		card_multiset_subset(m1 - multiset{x}, m2 - multiset{x});
	}
}

lemma suffix_multiset_subset<T>(s: seq<T>, k: int)
	requires 0 <= k < |s|
	ensures multiset(s[k..]) <= multiset(s)
{
	assert s == s[..k] + s[k..];
}

method getAllShuffledDataEntriesWithAvoidSet<T(==)>(m_workList: array<T>, avoidSet: set<T>)
	returns (result: array<T>)
	requires m_workList != null
	requires uniq(m_workList[..])
	requires m_workList.Length >= 2 * |avoidSet|
	ensures result != null
	ensures multiset(result[..]) == multiset(m_workList[..])
	ensures result.Length == m_workList.Length
	ensures uniq(result[..])
	ensures forall i :: 0 <= i < |avoidSet| ==> result[i] !in avoidSet
{
	result := new T[m_workList.Length];

	forall i | 0 <= i < m_workList.Length {
		result[i] := m_workList[i];
	}

	assert result[..] == m_workList[..];

	var n := |avoidSet|;
	var j := 0;
	var k := result.Length - 1;

	while (j <= k)
		decreases result.Length - j, k
		invariant j <= k + 1
		invariant -1 <= k < result.Length
		invariant n >= 0
		invariant multiset(result[..]) == multiset(m_workList[..])
		invariant n > 0 ==> forall i :: k < i < result.Length ==> result[i] in avoidSet
		invariant n > 0 ==> forall i :: 0 <= i < j ==> result[i] !in avoidSet
		invariant n > 0 ==> j + n == |avoidSet|
		invariant n == 0 ==> j >= |avoidSet|
		invariant n == 0 ==> forall i :: 0 <= i < |avoidSet| ==> result[i] !in avoidSet
	{
		var i := random(j, k);
		assert i >= j && i <= k;

		var e := result[i];

		if n > 0 && e in avoidSet {
			if i != k {
				swap(result, i, k);
			}

			k := k - 1;
		}
		else {
			if i != j {
				swap(result, i, j);
			}

			j := j + 1;

			if n > 0 {
				n := n - 1;

				if n == 0 {
					k := result.Length - 1;
				}
			}
		}
	}

	if n > 0 {
//		assert j == k + 1;
//		assert forall i :: k < i < result.Length ==> result[i] in avoidSet;
//		assert forall i :: 0 <= i <= k ==> result[i] !in avoidSet;

		calc {
			2 * |avoidSet| - k - 1;
			<= m_workList.Length - k - 1;
			== |multiset(result[k+1..])|;
			<= { suffix_multiset_subset(result[..], k + 1);
			    card_multiset_subset(multiset(result[k+1..]), multiset(avoidSet)); }
			|avoidSet|;
		}

//		assert |avoidSet| <= j; // a contradiction with j + n == |avoidSet| && n > 0
	}
}
