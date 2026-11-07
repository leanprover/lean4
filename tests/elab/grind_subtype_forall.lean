/-!
Quantifiers over a subtype are normalized with `Subtype.forall`/`Subtype.exists`, so a hypothesis
`∀ α : {a // p a}, q α` can be instantiated after `grind` splits the subtype binder of the goal.
-/

set_option warn.sorry false

abbrev Root := {n : Nat // n > 0}
variable (P Q : Nat → Prop)

example (h : ∀ α : Root, P α.val ∧ Q α.val) : ∀ α : Root, P α.val := by
  grind

example : ∀ α : Root, P α.val := by
  suffices h : ∀ α : Root, P α.val ∧ Q α.val by grind
  sorry

example (h : ∃ α : Root, P α.val) : ∃ n, n > 0 ∧ P n := by
  grind

example (h : ∃ n, n > 0 ∧ P n) : ∃ α : Root, P α.val := by
  grind

set_option backward.grind.normalizer false

example (h : ∀ α : Root, P α.val ∧ Q α.val) : ∀ α : Root, P α.val := by
  grind

example : ∀ α : Root, P α.val := by
  suffices h : ∀ α : Root, P α.val ∧ Q α.val by grind
  sorry

example (h : ∃ α : Root, P α.val) : ∃ n, n > 0 ∧ P n := by
  grind

example (h : ∃ n, n > 0 ∧ P n) : ∃ α : Root, P α.val := by
  grind
