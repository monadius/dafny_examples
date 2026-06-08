include "BinaryTree.dfy"

import opened BinaryTree

predicate GEAll(x: int, xs: multiset<int>)
{
    forall v :: v in xs ==> x >= v
}

lemma GEAllEmpty(x: int, xs: multiset<int>)
ensures |xs| == 0 ==> GEAll(x, xs)
{
}

predicate BinarySearchTree?(t: Tree<int>)
{
    match t
    case Nil => true
    case Node(x, l, r) => GEAll(x, ToMS(l)) && GEAll(x, ToMS(r)) && BinarySearchTree?(l) && BinarySearchTree?(r)
}
