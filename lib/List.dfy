module ListModule {

  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  function ToSeq<T>(xs: List<T>): seq<T> {
    if xs.Nil? then [] else [xs.head] + ToSeq(xs.tail)
  }

}

