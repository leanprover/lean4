
opaque f : Nat → Nat
-- A rewrite with a free variable on the RHS

opaque P : Nat → (Nat → Nat) → Prop
opaque Q : Nat → Prop
opaque foo (g : Nat → Nat) (x : Nat) : P x f ↔ Q (g x) := sorry

example : P x f ↔ Q (x + 10) := by
  rewrite [foo]
  -- we have an mvar in the goal now

  -- exact fails to close it (as it does not do approxDefEq)
  fail_if_success with_reducible exact Iff.rfl
  -- so `rfl` shouldn't either
  fail_if_success rfl
  -- but note that apply can close it:
  with_reducible(apply (Iff.rrfl)
