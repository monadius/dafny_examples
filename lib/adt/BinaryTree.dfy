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

    function countBT<T>(x: T, t: Tree<T>): nat {
        match t
        case Nil => 0
        case Node(y, l, r) =>
            (if x == y then 1 else 0) + countBT(x, l) + countBT(x, r)
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
    lemma countMSEq<T>(t : Tree<T>)
    ensures forall x :: member?(x, t) ==> x in toMS(t) && toMS(t)[x] == count(x, t)
    {
        forall x { memberInToMS(x, t); }
        match t {
            case Nil => assume false;
            case Node(y, l, r) => {
                assert member?(y, t);
                assert toMS(t)[y] == 1 + toMS(l)[y] + toMS(r)[y];
                assert count(y, t) == 1 + count(y, l) + count(y, r);
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

    lemma preorderFlattenPerm<T>(t: Tree<T>)
    ensures forall x :: countBT(x, t) == countSeq(x, preorderFlatten(t))
    {
        match t {
            case Nil => assert forall x :: countBT(x, t) == countSeq(x, preorderFlatten(t));
            case Node(y, l , r) => {
                preorderFlattenPerm(l);
                preorderFlattenPerm(r);
                assert forall x :: x == y ==>
                    1 + countBT(x, l) + countBT(x, r) ==
                        1 + countSeq(x, preorderFlatten(l)) + countSeq(x, preorderFlatten(r));
                assert forall x :: x != y ==>
                    countBT(x, l) + countBT(x, r) ==
                        countSeq(x, preorderFlatten(l)) + countSeq(x, preorderFlatten(r));
                assert forall x :: x == y ==> countBT(x, t) == 1 + countBT(x, l) + countBT(x, r);
                assert forall x :: x != y ==> countBT(x, t) == countBT(x, l) + countBT(x, r);
                assert forall x :: x == y ==> countSeq(x, preorderFlatten(t)) ==
                    1 + countSeq(x, preorderFlatten(l)) + countSeq(x, preorderFlatten(r));
                assert forall x :: x != y ==> countSeq(x, preorderFlatten(t)) ==
                    countSeq(x, preorderFlatten(l)) + countSeq(x, preorderFlatten(r));
                assume false;
            }
            
        }
        //notMemberCount0(t);
        //notMemberBTEqNotMemberIOFlatten(t);
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