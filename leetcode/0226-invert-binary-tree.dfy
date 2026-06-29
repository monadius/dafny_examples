// Author: Shaobo He
include "../lib/adt/BinaryTree.dfy"

import opened BinaryTree

function Mirror<T>(t: Tree<T>) : Tree<T>
{
    match t
    case Nil => Nil
    case Node(x, l, r) => Node(x, Mirror(r), Mirror(l))
}

// TODO: figure out why post condition doesn't work
lemma MirrorEq<T>(t: Tree<T>)
ensures Equal?(t, Mirror(Mirror(t)))
{
}

lemma MirrorPerm<T>(t: Tree<T>)
ensures forall x :: CountBT(x, t) == CountBT(x, Mirror(t))
{
}