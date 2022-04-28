// Author: Shaobo He
// Functional Binary Tree

module BinaryTree {
    datatype Tree<T> = Nil | Node(value: T, left: Tree<T>, right: Tree<T>)

    predicate member?<T>(x: T, t: Tree<T>) {
        match t
        case Nil => false
        case Node(y, l, r) => x == y || member?(x, l) || member?(x, r)
    }

    function size<T>(t: Tree<T>) : nat {
        match t
        case Nil => 0
        case Node(_, l, r) => 1 + size(l) + size(r)
    }

    function depth<T>(t: Tree<T>) : nat {
        match t
        case Nil => 0
        case Node(_, l, r) => 1 + 1 + (if depth(l) > depth(r) then depth(l) else depth(r))
    }

    predicate equal?<T>(t1: Tree<T>, t2: Tree<T>) {
        match t1
        case Nil => t2.Nil?
        case Node(v1, l1, r1) =>
            match t2
            case Nil => false
            case Node(v2, l2, r2) => v1 == v2 && equal?(l1, l2) && equal?(r1, r2)
    }

    lemma treeIdentityEqual<T>(t: Tree<T>)
    ensures equal?(t, t)
    {

    }

    lemma NilNotEqNode<T>(t1: Tree<T>, t2: Tree<T>)
    requires t1.Nil? && t2.Node?
    ensures !equal?(t1, t2)
    {

    }

    predicate isLeaf?<T>(t: Tree<T>) {
        t.Node? && t.left.Nil? && t.right.Nil?
    }

    lemma leafNodeEqual<T>(t1: Tree<T>, t2: Tree<T>)
    requires isLeaf?(t1) && isLeaf?(t2) && t1.value == t2.value
    ensures equal?(t1, t2)
    {

    }

    function mirror<T>(t: Tree<T>) : Tree<T>
    //ensures size(t) == size(mirror(t));
    //ensures depth(t) == depth(mirror(t));
    //ensures equal?(t, mirror(mirror(t)));
    {
        match t
        case Nil => Nil
        case Node(x, l, r) => Node(x, mirror(r), mirror(l))
    }

    lemma mirrorPerm<T>(t: Tree<T>)
    ensures forall x :: countBT(x, t) == countBT(x, mirror(t))
    {

    } 

    function countBT<T>(x: T, t: Tree<T>): nat {
        match t
        case Nil => 0
        case Node(y, l, r) =>
            (if x == y then 1 else 0) + countBT(x, l) + countBT(x, r)
    }

    lemma memberCountGE1<T>(x : T, t: Tree<T>)
    requires member?(x, t)
    ensures countBT(x, t) >= 1
    {

    }

    function toMS<T>(t: Tree<T>): multiset<T> {
        match t
        case Nil => multiset{}
        case Node(x, l, r) => multiset{x} + toMS(l) + toMS(r)
    }

    lemma memberInToMS<T>(x: T, t: Tree<T>)
    ensures member?(x, t) ==> x in toMS(t)
    {

    }
    
    /*
    lemma countMSEq<T>(x: T, t : Tree<T>)
    ensures member?(x, t) ==> x in toMS(t) && toMS(t)[x] == countBT(x, t)
    {
        forall x { memberInToMS(x, t); }
        match t {
            case Nil => assert true;
            case Node(y, l, r) => {
                // Shaobo: TODO proof
                assume false;
            }
        }
    }
    */

    // Borrow from Alexey's old write up for CS6110
    function countSeq<T>(x: T, s: seq<T>): nat
    {
        if (|s| == 0) then
            0
        else if x == s[0] then
            1 + countSeq(x, s[1..])
        else
            countSeq(x, s[1..])
    }

    function inorderFlatten<T>(t: Tree<T>) : seq<T>
    {
        match t
        case Nil => []
        case Node(x, l, r) => inorderFlatten(l) + [x] + inorderFlatten(r)
    }

    lemma notMemberCount0<T>(t: Tree<T>)
    ensures forall x :: !member?(x, t) <==> countBT(x, t) == 0
    {

    }

    lemma notMemberBTEqNotMemberIOFlatten<T>(t: Tree<T>)
    ensures forall x :: !member?(x, t) <==> x !in inorderFlatten(t)
    {

    }

    lemma countRecAppend<T>(x: T, s1: seq<T>, s2: seq<T>)
    ensures countSeq(x, s1) + countSeq(x, s2) == countSeq(x, s1 + s2)
    {
        if |s1| == 0 {
            assert s1 + s2 == s2;
        } else {
        // Shaobo: it seems the distributivity of list append is important here
            assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        }
    }

    lemma preorderFlattenPerm<T>(x: T, t: Tree<T>)
    ensures countBT(x, t) == countSeq(x, preorderFlatten(t))
    {
        match t {
            case Nil => assert forall x :: countBT(x, t) == countSeq(x, preorderFlatten(t));
            case Node(y, l , r) => {
                var lf := preorderFlatten(l);
                var rf := preorderFlatten(r);
                var f := preorderFlatten(t);
                assert f == [y] + (lf + rf);
                countRecAppend(x, lf, rf);
            }
        }
    }

    function preorderFlatten<T>(t: Tree<T>) : seq<T>
    {
        match t
        case Nil => []
        case Node(x, l, r) => [x] + preorderFlatten(l) + preorderFlatten(r)
    }

    function postorderFlatten<T>(t: Tree<T>) : seq<T>
    {
        match t
        case Nil => []
        case Node(x, l, r) => postorderFlatten(l) + postorderFlatten(r)
    }

}