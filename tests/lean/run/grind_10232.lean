def U {shape : Std.PRange.RangeShape} (b : Std.PRange.Bound shape.upper α) : Unit := sorry

structure T (l : α) : Type u where

def mysorry : α := sorry -- instead of `mysorry`, we could also use `sorry`.

example (inv : (T (U (shape := ⟨.closed, .closed⟩) 1)) → Prop)
    (h : inv mysorry) : True := by
  grind
