example (f : Fin n → Prop) (h : ∀ i h, i = 0 → f ⟨i, h⟩) : f i := by
  apply h
  rw [show i.1 = 0 from sorry]

def foo (x : Fin n) : Nat :=
  match x with
  | ⟨i, _⟩ => 5 + i

example (x : Fin n) : foo x = 5 := by
  simp [foo]
  rw [show x.1 = 0 from sorry]
