/-!
Regression test for #15747: `grind` failed on `(∀ x : Subtype P, Q x) → (∀ x : Subtype P, Q x)`.
The `[grind cases eager]` annotation on `Subtype` splits the goal's binder into `val` and
`property`, so the hypothesis' E-matching pattern `Subtype.val ?x` never matched. Quantifiers over
a subtype are now normalized with `Subtype.forall`/`Subtype.exists`.
-/

opaque A : Type
opaque P : A → Prop
opaque Q : A → Prop

example : (∀ x : Subtype P, Q x) → (∀ x : Subtype P, Q x) := by grind

example (h : ∀ x : Subtype P, Q x) (a : A) (ha : P a) : Q a := by grind

example (h : ∃ x : Subtype P, Q x) : ∃ a, P a ∧ Q a := by grind

set_option backward.grind.normalizer false

example : (∀ x : Subtype P, Q x) → (∀ x : Subtype P, Q x) := by grind

example (h : ∀ x : Subtype P, Q x) (a : A) (ha : P a) : Q a := by grind

example (h : ∃ x : Subtype P, Q x) : ∃ a, P a ∧ Q a := by grind
