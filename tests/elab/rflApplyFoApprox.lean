
opaque f : Nat → Nat
-- A rewrite with a free variable on the RHS

opaque P : Nat → (Nat → Nat) → Prop
opaque Q : Nat → Prop
opaque foo (g : Nat → Nat) (x : Nat) : P x f ↔ Q (g x) := sorry

example : P x f ↔ Q (x + 10) := by
  rewrite [foo]
  -- we have an mvar now
  with_reducible rfl -- should instantiate it with the lambda on the RHS and close the goal
  -- same as
  -- with_reducible (apply (Iff.refl _))
  -- NB: apply, not exact! Different defEq flags.
