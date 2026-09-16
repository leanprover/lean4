import Std.Tactic.BVDecide

namespace A

@[ext]
structure S (α : Type u) where
  x : α
  a : BitVec 8

example (x : S (BitVec 8)) : { x with a := x.a + 1 - 1 } = x := by
  bv_decide

end A

namespace B

class Injects (H : Type u) (X : outParam (Type v)) where
  coe : H → X
  injective : Function.Injective coe

@[ext] theorem Injects.ext {H : Type u} {X : Type v} [Injects H X]
    {a b : H} (h : Injects.coe a = Injects.coe b) : a = b := Injects.injective h

@[ext 1001]
structure S where
  a : BitVec 8

example (x : S) : ({ a := x.a + 1 - 1 } : S) = x := by
  bv_decide

end B

namespace C

class Injects (H : Type u) (X : outParam (Type v)) where
  coe : H → X
  injective : Function.Injective coe

@[ext] theorem Injects.ext {H : Type u} {X : Type v} [Injects H X]
    {a b : H} (h : Injects.coe a = Injects.coe b) : a = b := Injects.injective h

@[ext 1]
structure S where
  a : BitVec 8

example (x : S) : ({ a := x.a + 1 - 1 } : S) = x := by
  bv_decide

end C
