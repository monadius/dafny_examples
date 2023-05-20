// Author: Shaobo He
// Functional Binary Tree
include "../seq/Count.dfy"

module BinaryTree {
  import opened SeqCount

  datatype Tree<T> = Nil | Node(value: T, left: Tree<T>, right: Tree<T>)

  predicate Member?<T(==)>(x: T, t: Tree<T>) {
    match t
    case Nil => false
    case Node(y, l, r) => x == y || Member?(x, l) || Member?(x, r)
  }

  function Size<T>(t: Tree<T>) : nat {
    match t
    case Nil => 0
    case Node(_, l, r) => 1 + Size(l) + Size(r)
  }

  function Depth<T>(t: Tree<T>) : nat {
    match t
    case Nil => 0
    case Node(_, l, r) => 1 + (if Depth(l) > Depth(r) then Depth(l) else Depth(r))
  }

  predicate Equal?<T(==)>(t1: Tree<T>, t2: Tree<T>) {
    match t1
    case Nil => t2.Nil?
    case Node(v1, l1, r1) =>
      match t2
      case Nil => false
      case Node(v2, l2, r2) => v1 == v2 && Equal?(l1, l2) && Equal?(r1, r2)
  }

  lemma TreeIdentityEqual<T>(t: Tree<T>)
    ensures Equal?(t, t)
  {
  }

  lemma NilNotEqNode<T>(t1: Tree<T>, t2: Tree<T>)
    ensures t1.Nil? && t2.Node? ==> !Equal?(t1, t2)
  {
  }

  predicate IsLeaf?<T>(t: Tree<T>) {
    t.Node? && t.left.Nil? && t.right.Nil?
  }

  lemma LeafNodeEqual<T>(t1: Tree<T>, t2: Tree<T>)
    ensures IsLeaf?(t1) && IsLeaf?(t2) && t1.value == t2.value ==> Equal?(t1, t2)
  {
  }

  function CountBT<T(==)>(x: T, t: Tree<T>): nat {
    match t
    case Nil => 0
    case Node(y, l, r) =>
      (if x == y then 1 else 0) + CountBT(x, l) + CountBT(x, r)
  }

  lemma EqualImpSameCount<T>(t1: Tree<T>, t2: Tree<T>)
    requires Equal?(t1, t2)
    ensures forall x :: CountBT(x, t1) == CountBT(x, t2)
  {
  }

  lemma EqualImpSameCountImp<T>(t1: Tree<T>, t2: Tree<T>)
    ensures Equal?(t1, t2) ==> forall x :: CountBT(x, t1) == CountBT(x, t2)
  {
    if Equal?(t1, t2) {
      EqualImpSameCount(t1, t2);
    }
  }

  lemma MemberCountGE1<T>(x : T, t: Tree<T>)
    ensures Member?(x, t) ==> CountBT(x, t) >= 1
  {
  }

  function ToMS<T>(t: Tree<T>): multiset<T> {
    match t
    case Nil => multiset{}
    case Node(x, l, r) => multiset{x} + ToMS(l) + ToMS(r)
  }

  lemma MemberInToMS<T>(x: T, t: Tree<T>)
    ensures Member?(x, t) ==> x in ToMS(t)
  {
  }

  function InorderFlatten<T>(t: Tree<T>) : seq<T>
  {
    match t
    case Nil => []
    case Node(x, l, r) => InorderFlatten(l) + [x] + InorderFlatten(r)
  }

  lemma NotMemberCount0<T>(t: Tree<T>)
    ensures forall x :: !Member?(x, t) <==> CountBT(x, t) == 0
  {

  }

  lemma NotMemberBTEqNotMemberIOFlatten<T>(t: Tree<T>)
    ensures forall x :: !Member?(x, t) <==> x !in InorderFlatten(t)
  {

  }

  lemma PreorderFlattenPerm<T>(x: T, t: Tree<T>)
    ensures CountBT(x, t) == Count(PreorderFlatten(t), x)
  {
    match t {
      case Nil => assert forall x :: CountBT(x, t) == Count(PreorderFlatten(t), x);
      case Node(y, l , r) => {
        var lf := PreorderFlatten(l);
        var rf := PreorderFlatten(r);
        var f := PreorderFlatten(t);
        assert f == [y] + (lf + rf);
        CountConcat(lf, rf, x);
      }
    }
  }

  function PreorderFlatten<T>(t: Tree<T>) : seq<T>
  {
    match t
    case Nil => []
    case Node(x, l, r) => [x] + PreorderFlatten(l) + PreorderFlatten(r)
  }

  function PostorderFlatten<T>(t: Tree<T>) : seq<T>
  {
    match t
    case Nil => []
    case Node(x, l, r) => PostorderFlatten(l) + PostorderFlatten(r) + [x]
  }
}