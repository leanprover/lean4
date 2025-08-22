inductive D : Nat -> Type
def mwe (t : Nat) (f : Nat -> Nat) (h : f t = t)
  (d : D (f t))
  (P : (t : Nat) -> D t -> Prop)
  : P (f t) d
  := by
  rw [h] -- tactic 'rewrite' failed, motive is not type correct
  sorry

def K (x : α) (y : β) : β := y
example (h : true = false) (A : (b : Bool) → K b Type) (h2 : A false) : A true := by
  -- the motive is dependent on `true`, but in a non-essential way, so this works fine
  rw [h]
  exact h2

example (h : true = false) (A : (b : Bool) → if b then Prop else Nat) : A true :=
  by
    rw [h] -- tactic 'rewrite' failed, motive is dependent
    exact 0
