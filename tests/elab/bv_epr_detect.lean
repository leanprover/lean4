import Std.Tactic.BVDecide

/-!
Tests for the detection of many-sorted EPR problems in the `bv_normalize` pipeline, enabled through
`bv_decide`'s `epr` option.
-/

set_option trace.Meta.Tactic.bv.epr true

-- A single sort with a ground and a quantified fact.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a, b]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] ground fact: ¬P a
  [Meta.Tactic.bv.epr] ground fact: ¬a = b
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a b : α) (P : α → Prop) (h1 : ∀ x, P x) (h2 : ¬P a) (h3 : a ≠ b) : False := by
  bv_normalize +epr
  sorry

-- Multiple sorts, binary predicates, multiple quantifiers and the negated goal.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] sort β with elements [b₁, b₂]
  [Meta.Tactic.bv.epr] predicate R over [α, β]
  [Meta.Tactic.bv.epr] predicate Q over [β]
  [Meta.Tactic.bv.epr] ground fact: ¬(R a b₁ ∨ b₁ = b₂)
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α) (y : β), R x y → Q y ∨ y = b₁
  [Meta.Tactic.bv.epr] quantified fact: ∀ (y : β), Q y ↔ y = b₂
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (β : Type 1) (a : α) (b₁ b₂ : β) (R : α → β → Prop) (Q : β → Prop)
    (h1 : ∀ x y, R x y → Q y ∨ y = b₁) (h2 : ∀ y, Q y ↔ y = b₂) : R a b₁ ∨ b₁ = b₂ := by
  bv_normalize +epr
  sorry

-- Propositional atoms may occur in facts but are not predicates of the problem.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] ground fact: ¬¬P a
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x → q
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a : α) (P : α → Prop) (q r : Prop) (h1 : ∀ x, P x → q) (h2 : r) : ¬P a := by
  bv_normalize +epr
  sorry

-- A sort without constants obtains one from a `Nonempty` instance.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [Classical.ofNonempty]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), ¬P x
-/
#guard_msgs (trace, drop warning) in
example (α : Type) [Nonempty α] (P : α → Prop) (h1 : ∀ x, P x) (h2 : ∀ x, ¬P x) : False := by
  bv_normalize +epr
  sorry

-- Facts over a sort without constants and without a `Nonempty` instance are discarded.
/--
trace: [Meta.Tactic.bv.epr] Discarding fact as it mentions empty sorts: ∀ (x : α), P x
[Meta.Tactic.bv.epr] Discarding fact as it mentions empty sorts: ∀ (x : α), ¬P x
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (P : α → Prop) (h1 : ∀ x, P x) (h2 : ∀ x, ¬P x) : False := by
  bv_normalize +epr
  sorry

-- Hypotheses using function symbols are not part of the problem.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] sort β with elements [b]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] predicate Q over [β]
  [Meta.Tactic.bv.epr] ground fact: ¬Q b
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x
-/
#guard_msgs (trace, drop warning) in
example (α β : Type) (a : α) (b : β) (f : α → α) (P : α → Prop) (Q : β → Prop)
    (h1 : ∀ x, P x) (h2 : ¬Q b) (h3 : P (f a)) : False := by
  bv_normalize +epr
  sorry

-- Hypotheses outside of the EPR fragment are not part of the problem.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] sort β with elements [b]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] predicate Q over [β]
  [Meta.Tactic.bv.epr] predicate R over [α, β]
  [Meta.Tactic.bv.epr] ground fact: Q b
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x
  [Meta.Tactic.bv.epr] quantified fact: ∀ (y : β), R a y
-/
#guard_msgs (trace, drop warning) in
example (α β : Type) (a : α) (b : β) (P : α → Prop) (Q : β → Prop) (R : α → β → Prop)
    (h1 : ∀ x, P x) (h2 : ∀ y, R a y) (h3 : ∀ y, ∃ x, R x y) (h4 : Q b) : False := by
  bv_normalize +epr
  sorry

-- Nested quantifiers are not supported.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] ground fact: P a
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a : α) (P : α → Prop) (h1 : P a → ∀ x, P x) (h2 : P a) : False := by
  bv_normalize +epr
  sorry

-- Structures and instances do not affect the problem.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] ground fact: ¬P a
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x ∨ x = a
-/
#guard_msgs (trace, drop warning) in
example (α : Type) [DecidableEq α] [Inhabited α] (a : α) (p : α × Nat) (P : α → Prop)
    (h1 : ∀ x, P x ∨ x = a) (h2 : ¬P a) : False := by
  bv_normalize +epr
  sorry

-- Universe polymorphic sorts.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] predicate P over [α, α]
  [Meta.Tactic.bv.epr] ground fact: P a a
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x y : α), P x y → P y x
-/
#guard_msgs (trace, drop warning) in
example (α : Type u) (a : α) (P : α → α → Prop) (h1 : ∀ x y, P x y → P y x) (h2 : P a a) : False := by
  bv_normalize +epr
  sorry

-- Purely propositional and `BitVec` hypotheses do not constitute an EPR problem.
#guard_msgs (trace, drop warning) in
example (p : Prop) (x : BitVec 8) (h1 : p) (h2 : x + 1 = 0) : False := by
  bv_normalize +epr
  sorry

-- Without the option nothing is detected.
#guard_msgs (trace, drop warning) in
example (α : Type) (a : α) (P : α → Prop) (h1 : ∀ x, P x) (h2 : ¬P a) : False := by
  bv_normalize
  sorry

-- Implications that refer to the leading quantifiers and equalities between propositions.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort α with elements [a]
  [Meta.Tactic.bv.epr] predicate P over [α]
  [Meta.Tactic.bv.epr] predicate Q over [α]
  [Meta.Tactic.bv.epr] ground fact: P a
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x y : α), P x → P y → Q x
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), P x = Q x
  [Meta.Tactic.bv.epr] quantified fact: ∀ (x : α), Q x = False
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a : α) (P Q : α → Prop) (h1 : ∀ x y, P x → P y → Q x) (h2 : ∀ x, P x = Q x)
    (h3 : ∀ x, Q x = False) (h4 : P a) : False := by
  bv_normalize +epr
  sorry
