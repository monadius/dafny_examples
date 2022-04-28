// Author: Shaobo He
include "../lib/adt/BinaryTree.dfy"

import opened BinaryTree

method isMirror?<T(==)>(t1: Tree<T>, t2: Tree<T>) returns(r: bool)
ensures r <==> equal?(t1, mirror(t2));
{
    if (t1.Nil? && t2.Nil?) {
        return true;
    }
    if (t1.Nil? || t2.Nil?) {
        return false;
    }
    var m1 := isMirror?(t1.right, t2.left);
    var m2 := isMirror?(t1.left, t2.right);
    return t1.value == t2.value && m1 && m2;
}

method isSymmetric<T(==)>(root: Tree<T>) returns(r: bool)
ensures r <==> equal?(root, mirror(root));
{
    r := isMirror?(root, root);
}