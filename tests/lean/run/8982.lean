/-! Test that unsound unification hints are rejected -/

/-! When the conclusion is not implied by the premises, the unification hint should be rejected -/

/--
error: invalid unification hint, failed to unify pattern left-hand-side
  f a
with right-hand-side
  b
-/
#guard_msgs in
unif_hint (f : α → β) (a : α) (b : β) where ⊢ f a ≟ b

/--
error: invalid unification hint, failed to unify pattern left-hand-side
  x
with right-hand-side
  y
-/
#guard_msgs in
unif_hint (x y : α) where ⊢ x ≟ y

/--
error: invalid unification hint, failed to unify pattern left-hand-side
  true
with right-hand-side
  b
-/
#guard_msgs in
unif_hint {b : Bool} where ⊢ true ≟ b

/-! If a premise is not an assignment to a variable, the hint should be rejected -/

abbrev const (_ : Type) : Unit := ()

/--
error: invalid unification hint, constraint
  const x =?= const y
does not contain a variable on either side
-/
#guard_msgs in
unif_hint (x y : Type) where const x ≟ const y ⊢ x ≟ y

/-! If a variable is already assigned, a premise assigning to it again should be rejected -/

/--
error: invalid unification hint, constraint
  const x =?= const y
does not contain a variable on either side
-/
#guard_msgs in
unif_hint (x y : Type) (u : Unit) where
  u ≟ const x
  u ≟ const y
  ⊢ x ≟ y

/-! If the assignments form a cycle, the hint should be rejected -/

/--
error: invalid unification hint, cyclic constraint
  x =?= x.succ
-/
#guard_msgs in
unif_hint (x : Nat) where
  x ≟ x.succ
  ⊢ x ≟ x.succ

/--
error: invalid unification hint, cyclic constraint
  x.succ =?= x
-/
#guard_msgs in
unif_hint (x y : Nat) where
  y ≟ x
  x.succ ≟ y
  ⊢ x ≟ x.succ
