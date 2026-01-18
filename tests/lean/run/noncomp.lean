noncomputable def foo : Nat := Classical.choose (show ∃ x, x = 1 from ⟨1, rfl⟩)

structure Bar (n : Nat) where
  x : Nat

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'foo', which is 'noncomputable'
-/
#guard_msgs in
def baz : Bar foo :=
  { x := 1 }

structure Bar2 (n : Nat) where
  x : Nat
  y : Nat

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'foo', which is 'noncomputable'
-/
#guard_msgs in
def bax2 : Bar2 foo :=
  { x := 1, y := 2 }
