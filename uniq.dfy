predicate uniq_mult1<T>(s: seq<T>)
{
	forall t :: t in s ==> multiset(s)[t] == 1
}

predicate uniq_mult2<T>(s: seq<T>)
{
	forall t :: t in s ==> multiset(s)[t] <= 1
}

predicate uniq_distinct<T>(s: seq<T>)
{
	forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
}

predicate uniq_ind<T>(s: seq<T>)
{
	if s == [] then true else s[0] !in s[1..] && uniq_ind(s[1..])
}

lemma lemma1<T>(s: seq<T>)
	ensures uniq_ind(s) <==> uniq_distinct(s)
{
}

lemma lemma2<T>(s: seq<T>)
	ensures uniq_mult1(s) <==> uniq_mult2(s)
{
}

function count_eq<T>(x: T, s: seq<T>): nat
{
	if s == [] then
		0
	else if s[0] == x then
		1 + count_eq(x, s[1..])
	else
		count_eq(x, s[1..])
}

lemma count0<T>(x: T, s: seq<T>)
	requires x !in s
	ensures count_eq(x, s) == 0
{
}

lemma count_in<T>(x: T, s: seq<T>)
	ensures 0 < count_eq(x, s) <==> x in s
{
}

lemma uniq_count<T>(x: T, s: seq<T>)
	requires uniq_ind(s)
	requires x in s
	ensures count_eq(x, s) == 1
{
	if s == [] {
	}
	else if x == s[0] {
		calc {
			count_eq(x, s);
			1 + count_eq(x, s[1..]);
			{ count0(x, s[1..]); }
			1;
		}
	}
	else {
//		uniq_count(x, s[1..]);
	}
}

lemma count_append<T>(x: T, s1: seq<T>, s2: seq<T>)
	ensures count_eq(x, s1 + s2) == count_eq(x, s1) + count_eq(x, s2)
{
	if s1 == [] {
		assert s1 + s2 == s2;
	}
	else {
		calc {
			count_eq(x, s1 + s2);
			{ assert s1 + s2 == [s1[0]] + (s1[1..] + s2); }
			count_eq(x, [s1[0]] + (s1[1..] + s2));
		}
	}
}

lemma count1_uniq<T>(s: seq<T>)
	requires forall x :: x in s ==> count_eq(x, s) == 1
	ensures uniq_ind(s)
{
	if s == [] {
	}
	else {
		calc <==> {
			s[0] in s[1..];
			{ count_in(s[0], s[1..]); }
			count_eq(s[0], s[1..]) > 0;
			count_eq(s[0], s) - 1 > 0; // a contradiction!
		}

		assert s[0] !in s[1..];
		forall x | x in s[1..] ensures count_eq(x, s[1..]) == 1 {
			assert x in s;
		}
		count1_uniq(s[1..]);
	}
}

lemma in_uniq_append<T>(x: T, s1: seq<T>, s2: seq<T>)
	requires uniq_ind(s1 + s2)
	ensures x in s1 ==> x !in s2
	ensures x in s2 ==> x !in s1
{
	if x in s1 && x in s2 {
		calc <==> {
			x in s2;
		  { count_in(x, s2); }
			count_eq(x, s2) > 0;
		  { count_append(x, s1, s2); }
			count_eq(x, s1 + s2) - count_eq(x, s1) > 0;
		  { uniq_count(x, s1 + s2); }
			1 > count_eq(x, s1);
		  { count_in(x, s1); }
			false;
		}
	}
/*
	if x in s1 {
		var i :| 0 <= i < |s1| && s1[i] == x;
		if x in s2 {
			var j :| 0 <= j < |s2| && s2[j] == x;
			assert (s1 + s2)[|s1| + j] == x;
			lemma1(s1 + s2);
		}
	}
*/
}

lemma uniq_sub_aux<T>(x: T, s: seq<T>, a: int, b: int)
	requires uniq_ind(s)
	requires 0 <= a < b <= |s|
	requires x in s[a..b]
	ensures count_eq(x, s[a..b]) == 1
{
	//	assume x !in s[..a] && x !in s[b..];
	assert s == s[..a] + s[a..];
	in_uniq_append(x, s[..a], s[a..]);
	assert x !in s[..a];

	assert s == s[..b] + s[b..];
	in_uniq_append(x, s[..b], s[b..]);
	assert x !in s[b..];

	calc {
		1;
		{ uniq_count(x, s); }
		count_eq(x, s);
		{ assert s == s[..a] + (s[a..b] + s[b..]); }
		count_eq(x, s[..a] + (s[a..b] + s[b..]));
		{ count_append(x, s[..a], s[a..b] + s[b..]); }
		count_eq(x, s[..a]) + count_eq(x, s[a..b] + s[b..]);
		{ count_append(x, s[a..b], s[b..]); }
		count_eq(x, s[..a]) + count_eq(x, s[a..b]) + count_eq(x, s[b..]);
		calc {
			count_eq(x, s[..a]);
			{ count0(x, s[..a]); }
			0;
		}
		calc {
			count_eq(x, s[b..]);
			{ count0(x, s[b..]); }
			0;
		}
		count_eq(x, s[a..b]);
	}
}

lemma uniq_sub<T>(s: seq<T>, a: int, b: int)
	requires uniq_ind(s)
	requires 0 <= a < b <= |s|
	ensures uniq_ind(s[a..b])
{
	forall x | x in s[a..b] {
		uniq_sub_aux(x, s, a, b);
	}

	count1_uniq(s[a..b]);
}

lemma count_multiset<T>(x: T, s: seq<T>)
	ensures count_eq(x, s) == multiset(s)[x]
{
	if s == [] {
	}
	else {
		assert s == [s[0]] + s[1..];
//		calc {
//			count_eq(x, s);
//			(if x == s[0] then 1 else 0) + count_eq(x, s[1..]);
//			multiset{s[0]}[x] + multiset(s[1..])[x];
//			{ assert s == [s[0]] + s[1..]; }
//			multiset(s)[x];
//		}
	}
}


lemma lemma3<T>(s: seq<T>)
	ensures uniq_ind(s) <==> uniq_mult1(s)
{
	if uniq_ind(s) {
		forall x | x in s ensures multiset(s)[x] == 1 {
			calc {
				multiset(s)[x];
				{ count_multiset(x, s); }
				count_eq(x, s);
				{ uniq_count(x, s); }
				1;
			}
		}
	}
	else if uniq_mult1(s) {
		forall x | x in s ensures count_eq(x, s) == 1 {
			calc {
				count_eq(x, s);
				{ count_multiset(x, s); }
				multiset(s)[x];
				1;
			}
		}

		count1_uniq(s);
	}
}


lemma lemma_all<T>(s: seq<T>)
	ensures uniq_ind(s) == uniq_distinct(s) == uniq_mult1(s) == uniq_mult2(s)
{
//	lemma1(s);
//	lemma2(s);
	lemma3(s);
}

lemma lemma4<T>(s: seq<T>)
	ensures uniq_ind(s) <==> uniq_mult2(s)
{
	lemma_all(s);
}
