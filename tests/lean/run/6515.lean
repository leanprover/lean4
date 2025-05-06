/-!
# `injection` and `contradiction` for types without `noConfusion` declarations

https://github.com/leanprover/lean4/issues/6515

These tests ensure that tactics that attempt to use no-confusion types do not do so for types for
which such declarations do not exist.
-/

set_option pp.proofs true

/--
error: tactic 'contradiction' failed
this : Or.inl trivial = Or.inr trivial
⊢ False
-/
#guard_msgs in
example : False := by
  have : Or.inl trivial = Or.inr trivial := rfl
  contradiction
  sorry

/--
error: tactic 'injection' failed, the type
  True ∨ True
lacks a no-confusion principle, so 'injection' cannot prove the injectivity or distinctness of its constructors
this : Or.inl trivial = Or.inr trivial
⊢ False
-/
#guard_msgs in
example : False := by
  have : Or.inl trivial = Or.inr trivial := rfl
  injection this
  sorry

/--
error: tactic 'contradiction' failed
this : HEq (Or.inl trivial) (Or.inr trivial)
⊢ False
-/
#guard_msgs in
example : False := by
  have : HEq (Or.inl trivial) (Or.inr trivial) := HEq.rfl
  contradiction
  sorry
