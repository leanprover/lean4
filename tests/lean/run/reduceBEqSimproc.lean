-- set_option trace.Elab.Deriving.lawfulBEq true

inductive L (α : Type u) where
  | nil  : L α
  | cons : α → L α → L α
deriving BEq

example {n m : Nat} (h : n = m) :
    (L.cons n (L.nil : L Nat) == L.cons m (L.nil : L Nat)) = true := by
  simp [reduceBEq]
  assumption
