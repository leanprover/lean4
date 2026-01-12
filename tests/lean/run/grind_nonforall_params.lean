/-
Tests `grind` proof parameters whose type is not a `forall`.
-/

opaque f : Nat → Nat
axiom le_f (a : Nat) : a ≤ f a

example (a : Nat) : a ≤ f a := by
  grind [le_f a]

example (a b : α) (h : ∀ x y : α, x = y) : a = b := by
  fail_if_success grind
  grind [h a b]

/--
error: invalid `grind` parameter, modifier is redundant since the parameter type is not a `forall`
  a ≤ f a
-/
#guard_msgs in
example (a : Nat) : a ≤ f a := by
  grind [← le_f a]
