/-! # Ensure `rw` prioritizes the local context over the environment

This test ensures that `rw [foo]` looks for `foo` in the local context before it looks for a
constant named `foo` in the environment. See issue #2729.
-/

-- Introduce `foo` to the environment.
/-- A constant whose name should conflict with that of a local declaration. -/
def foo : List Nat := [0]

/-! ## Ensure that `foo` from the LCtx is used instead of the constant `foo` -/

example (A B : Prop) (foo : A ↔ B) (b : B) : A := by
  rw [foo] -- should be interpreted as `foo : A ↔ B`, not `foo : List Nat`, and succeed
  assumption

/-! ## Ensure that we can access the constant `foo` by writing `rw [_root_.foo]` -/

set_option linter.unusedVariables false in
example (A B : Prop) (foo : A ↔ B) : _root_.foo = [0] := by
  rw [_root_.foo] -- should be interpreted as `foo : List Nat`, not `foo : A ↔ B`, and succeed
