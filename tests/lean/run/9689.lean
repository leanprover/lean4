class C1 (b : outParam Bool) (m : Type u → Type) where
  val : m α

class C2 (m : Type → Type) where
  val : m α

instance [C2 m] : C1 false m where
  val := C2.val

instance [C1 b m] : Inhabited (m α) where
  default := C1.val

def T (_ : Type u) := Unit

instance : C1 true T where
  val := ()

example : T α := default
example : T α := default_or_ofNonempty%

def U : Type u := PUnit

instance : Inhabited U.{0} where
  default := ()

example : U := default
example : U := default_or_ofNonempty%
