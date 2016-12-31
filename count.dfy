function count_eq<T(==)>(x: T, s: seq<T>): nat
{
	if s == [] then
		0
	else if s[0] == x then
		1 + count_eq(x, s[1..])
	else
		count_eq(x, s[1..])
}

lemma count0<T(==)>(x: T, s: seq<T>)
	requires x !in s
	ensures count_eq(x, s) == 0
{
}

lemma count_in<T(==)>(x: T, s: seq<T>)
	ensures 0 < count_eq(x, s) <==> x in s
{
}

lemma count_multiset<T(==)>(x: T, s: seq<T>)
	ensures count_eq(x, s) == multiset(s)[x]
{
	if s == [] {
	}
/*	
	else if x == s[0] {
		calc {
			count_eq(x, s);
			1 + count_eq(x, s[1..]);
			multiset{s[0]}[x] + count_eq(x, s[1..]);
			multiset{s[0]}[x] + multiset(s[1..])[x];
			multiset([s[0]] + s[1..])[x];
			{ assert s == [s[0]] + s[1..]; }
			multiset(s)[x];
		}
	} 
*/
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
