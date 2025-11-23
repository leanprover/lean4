/-!
# Make sure local instance detection can handle metavariables and other reductions
-/

/-!
Reported in https://github.com/leanprover/lean4/issues/2199
The `inferInstance` was failing due to metavariables introduced by `cases`.
-/
theorem exists_foo : ∃ T : Type, Nonempty T := ⟨Unit, ⟨()⟩⟩

example : True := by
  cases exists_foo
  rename_i T hT
  have : Nonempty T := inferInstance
  trivial

/-!
The `let` would inhibit `inst` from being seen as a local `Decidable` instance.
Two tests: one where `let` starts a telescope, and another where it's at the end.
(Having `let`s in the middle of a forall telescope always worked.)
-/
axiom p : Nat → Prop

axiom inst : let n := 5; Decidable (p n)

example : True := by
  have := inst
  have : Decidable (p 5) := inferInstance
  trivial

axiom inst' : ∀ k, let n := k; Decidable (p n)

example : True := by
  have := inst'
  have : Decidable (p 5) := inferInstance
  trivial

/-!
This worked before, but here's an extra test that abbreviations are correctly handled.
-/
abbrev D (p : Prop) := Decidable p

example (p : Prop) [D p] : (if p then True else False) ↔ p := by
  split <;> simp_all
