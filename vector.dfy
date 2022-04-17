/*
	abstract module Vec0 {
	class Vector<T> {
		ghost var contents: seq<T>

		protected predicate Valid()
			reads this

		constructor ()
			ensures contents == []

		method push_back(obj: T)
			requires Valid()
			ensures contents == old(contents) + [obj]
			ensures Valid()

		method size() returns (s: int)
			requires Valid()
			ensures contents == old(contents)
			ensures s == |contents|
			ensures Valid()
	}
}
*/

module Vec {
	class Vector<T(0)> {
		ghost var Contents: seq<T>;
		ghost var Repr: set<object>;
		
		var objs: array<T>;
		var capacity: int;
		var length: int;
			
		predicate Valid()
			reads this, objs
		{
			this in Repr && objs in Repr && 
				capacity == objs.Length &&
				0 <= length <= capacity &&
				1 <= capacity &&
				Contents == objs[..length]
		}

		constructor ()
			ensures Contents == []
			ensures Valid()
		{
			capacity := 1;
			length := 0;
			objs := new T[1];

			Contents := [];
			Repr := {this, objs};
		}

		method size() returns (s: int)
			requires Valid()
			ensures Contents == old(Contents) && Repr == old(Repr)
			ensures s == |Contents|
			ensures Valid()
		{
			s := length;
		}

		method resize(size: int)
			modifies Repr
			requires Valid()
			requires size > 0
			ensures size <= capacity
			ensures Contents == old(Contents)
			ensures Valid() && fresh(Repr - old(Repr))
		{
			if (size > capacity) {
				capacity := size;
				var newObjs := new T[capacity];

				forall i | 0 <= i < length {
					newObjs[i] := objs[i];
				}

				objs := newObjs;

				Repr := Repr + {newObjs};
			}
		}

		method push_back(obj: T)
			modifies Repr
			requires Valid()
			ensures Contents == old(Contents) + [obj]
			ensures Valid() && fresh(Repr - old(Repr))
		{
			if (length < capacity) {
				objs[length] := obj;
				length := length + 1;
			}
			else {
				/*
					 // Works without Repr:
				capacity := capacity * 2;
				var newObjs := new T[capacity];

				forall i | 0 <= i < length {
					newObjs[i] := objs[i];
				}

				objs := newObjs;
				 */
				resize(capacity * 2);

				assert capacity > length;
				assert objs.Length == capacity;
				assert objs.Length > length;
				
				objs[length] := obj;
				length := length + 1;
			}

			Contents := Contents + [obj];
		}
	}
}
