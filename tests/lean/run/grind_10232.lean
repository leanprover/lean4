inductive BoundShape where
  | «open» : BoundShape
  | closed : BoundShape
  | unbounded : BoundShape

structure RangeShape where
  lower : BoundShape
  upper : BoundShape

abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .unbounded => PUnit

def U {shape : RangeShape} (b : Bound shape.upper α) : Unit := sorry

structure T (l : α) : Type u where

def mysorry : α := sorry -- instead of `mysorry`, we could also use `sorry`.

example (inv : (T (U (shape := ⟨.closed, .closed⟩) 1)) → Prop)
    (h : inv mysorry) : True := by
  grind
