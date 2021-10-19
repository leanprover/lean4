noncomputable def foo : Nat := Classical.choose (show ∃ x, x = 1 from ⟨1, rfl⟩)

structure Bar (n : Nat) :=
  x : Nat

def baz : Bar foo :=
  { x := 1 }
