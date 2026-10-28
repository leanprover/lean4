import Std.Tactic.BVDecide

/-!
Tests that counterexamples to `bv_decide +epr` are reported in terms of the original EPR problem:
predicates are assigned `True` or `False`, elements of a sort `α` are assigned `αₙ`, and neither the
`BitVec` encoding nor its uninterpreted predicates are mentioned.
-/


/--
error: The prover found a counterexample, consider the following assignment:
P a = False
a = α₀
b = α₀
-/
#guard_msgs in
example (α : Type) (a b : α) (P : α → Prop) (h1 : ∀ x, P x ∨ x = a) (h2 : ¬P a) : False := by
  bv_decide +epr +uf

-- Multiple sorts and binary predicates.
/--
error: The prover found a counterexample, consider the following assignment:
R a b₁ = False
a = α₀
b₁ = β₀
b₂ = β₁
Q b₂ = True
-/
#guard_msgs in
example (α : Type) (β : Type 1) (a : α) (b₁ b₂ : β) (R : α → β → Prop) (Q : β → Prop)
    (h1 : ∀ x y, R x y → Q y ∨ y = b₁) (h2 : ∀ y, Q y ↔ y = b₂) : R a b₁ ∨ b₁ = b₂ := by
  bv_decide +epr +uf

-- Inaccessible sort names.
/--
error: The prover found a counterexample, consider the following assignment:
P✝ a✝¹ = False
a✝¹ = α₀✝
-/
#guard_msgs in
example : ∀ (α : Type) (a : α) (P : α → Prop), ¬P a → False := by
  intros
  bv_decide +epr +uf

-- Elements obtained from a `Nonempty` instance.
/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables:
  - Classical.ofNonempty
Consider the following assignment:
Classical.ofNonempty = α₀
-/
#guard_msgs in
example (α : Type) [Nonempty α] (P : α → Prop) (h1 : ∀ x, P x ∨ ¬P x) : False := by
  bv_decide +epr +uf

-- Mixed with `BitVec` variables and genuine uninterpreted functions.
/--
error: - The prover used the following expressions as uninterpreted functions:
  - f x
The prover found a counterexample, consider the following assignment:
f x = 1#8
P b = True
b = α₀
a = α₀
x = 0#8
-/
#guard_msgs in
example (α : Type) (a b : α) (P : α → Prop) (x : BitVec 8) (f : BitVec 8 → BitVec 8)
    (h1 : ∀ x, P x ∨ x = a) (h2 : f x = 1) (h3 : P b) : False := by
  bv_decide +epr +uf

-- Unused hypotheses mentioning EPR symbols are reported.
/--
error: The prover found a potentially spurious counterexample:
- The following potentially relevant hypotheses could not be used:
  - ∀ (y : β), ∃ x, R x y derived via assumption h2
Consider the following assignment:
b = β₀
a = α₀
R a b = True
-/
#guard_msgs in
example (α β : Type) (a : α) (b : β) (R : α → β → Prop) (h1 : ∀ x y, R x y) (h2 : ∀ y, ∃ x, R x y) :
    False := by
  bv_decide +epr +uf
