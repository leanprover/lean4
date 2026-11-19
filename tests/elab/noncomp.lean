noncomputable def foo : Nat := Classical.choose (show ∃ x, x = 1 from ⟨1, rfl⟩)

structure Bar (n : Nat) where
  x : Nat

def baz : Bar foo :=
  { x := 1 }

structure Bar2 (n : Nat) where
  x : Nat
  y : Nat

def bax2 : Bar2 foo :=
  { x := 1, y := 2 }
