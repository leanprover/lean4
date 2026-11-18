import Std.Tactic.BVDecide

/-!
Tests for the sort inference of `bv_decide +epr`, which splits a type into several sorts if their
elements never interact and keeps them together if a quantifier restricts their cardinality.
-/

section Traces

set_option trace.Meta.Tactic.bv.epr true

-- `d` never interacts with the other elements, which `P` and `Q` connect into one sort.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort 0 : α with elements [a, b, c]
  [Meta.Tactic.bv.epr] sort 3 : α with elements [d]
  [Meta.Tactic.bv.epr] predicate P over [(0, α)]
  [Meta.Tactic.bv.epr] predicate Q over [(0, α)]
  [Meta.Tactic.bv.epr] predicate R over [(3, α)]
  [Meta.Tactic.bv.epr] ground fact: a = b
  [Meta.Tactic.bv.epr] ground fact: P b
  [Meta.Tactic.bv.epr] ground fact: ¬Q c
  [Meta.Tactic.bv.epr] ground fact: R d
  [Meta.Tactic.bv.epr] quantified fact [0] : ∀ (x : α), P x → Q x
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (a b c d : α) (P Q R : α → Prop) (h1 : a = b) (h2 : ∀ x, P x → Q x) (h3 : P b)
    (h4 : ¬Q c) (h5 : R d) : False := by
  bv_normalize +epr
  sorry

-- A positive equality on quantified variables bounds the cardinality of `α` and prevents splitting
-- it, but `β` is still split.
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort 0 : β with elements [b₁]
  [Meta.Tactic.bv.epr] sort 1 : β with elements [b₂]
  [Meta.Tactic.bv.epr] sort 2 : α with elements [a₁, a₂]
  [Meta.Tactic.bv.epr] predicate P₁ over [(2, α)]
  [Meta.Tactic.bv.epr] predicate P₂ over [(2, α)]
  [Meta.Tactic.bv.epr] predicate Q₁ over [(0, β)]
  [Meta.Tactic.bv.epr] predicate Q₂ over [(1, β)]
  [Meta.Tactic.bv.epr] ground fact: P₁ a₁
  [Meta.Tactic.bv.epr] ground fact: P₂ a₂
  [Meta.Tactic.bv.epr] ground fact: Q₁ b₁
  [Meta.Tactic.bv.epr] ground fact: Q₂ b₂
  [Meta.Tactic.bv.epr] quantified fact [2, 2] : ∀ (x y : α), x = y
-/
#guard_msgs (trace, drop warning) in
example (α β : Type) (a₁ a₂ : α) (b₁ b₂ : β) (P₁ P₂ : α → Prop) (Q₁ Q₂ : β → Prop)
    (h1 : ∀ x y : α, x = y) (h2 : P₁ a₁) (h3 : P₂ a₂) (h4 : Q₁ b₁) (h5 : Q₂ b₂) : False := by
  bv_normalize +epr
  sorry

end Traces

section Unsat

variable (α : Type) (a b c : α) (P Q : α → Prop) (R : α → α → Prop)

-- `b` and `c` are only related through a quantifier whose class does not contain them.
example (h1 : ∀ x y : α, x = y) (h2 : P a) (h3 : Q b) (h4 : ¬Q c) : False := by
  bv_decide +epr +uf

-- The quantified class does not contain any elements but the sort is inhabited.
example (h1 : ∀ x, Q x) (h2 : ∀ y, ¬Q y) (h3 : P a) : False := by
  bv_decide +epr +uf

-- MBQI has to instantiate a quantified fact across sorts of different cardinalities.
example (u₁ u₂ : α) (h1 : R u₁ a) (h2 : ¬R u₂ a) (h3 : ∀ u u' x, R u x → R u' x) : False := by
  bv_decide +epr +uf

end Unsat

section Sat

-- Distinct sorts of one type may reuse a name.
/--
error: The prover found a counterexample, consider the following assignment:
Q b = True
b = α₀
P a = True
a = α₀
-/
#guard_msgs in
example (α : Type) (a b : α) (P Q : α → Prop) (h1 : ∀ x, P x) (h2 : Q b) (h3 : P a) : False := by
  bv_decide +epr +uf

/--
error: The prover found a counterexample, consider the following assignment:
P a = True
a = α₀
Q b = False
b = α₁
P b = False
Q a = True
-/
#guard_msgs in
example (α : Type) (a b : α) (P Q : α → Prop) (h1 : ∀ x, P x → Q x) (h2 : P a) (h3 : ¬Q b) :
    False := by
  bv_decide +epr +uf

end Sat
