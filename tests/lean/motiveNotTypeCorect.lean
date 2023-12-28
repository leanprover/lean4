inductive D : Nat -> Type
def mwe (t : Nat) (f : Nat -> Nat) (h : f t = t)
  (d : D (f t))
  (P : (t : Nat) -> D t -> Prop)
  : P (f t) d
  := by
  rw [h] -- tactic 'rewrite' failed, motive is not type correct
  sorry
