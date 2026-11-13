import Std.Tactic.BVDecide

/-!
Tests for `bv_decide +epr`: detection of many-sorted EPR problems, proofs that need equality
reasoning and MBQI, and counterexamples reported in terms of the original problem.
-/

-- Detection of sorts, predicates, ground and quantified facts, ignoring facts outside the fragment.
set_option trace.Meta.Tactic.bv.epr true in
/--
trace: [Meta.Tactic.bv.epr] ✅️ Detected EPR problem
  [Meta.Tactic.bv.epr] sort 0 : β with elements [b₁, b₂]
  [Meta.Tactic.bv.epr] sort 2 : α with elements [a]
  [Meta.Tactic.bv.epr] predicate R over [(2, α), (0, β)]
  [Meta.Tactic.bv.epr] predicate Q over [(0, β)]
  [Meta.Tactic.bv.epr] ground fact: ¬(R a b₁ ∨ b₁ = b₂)
  [Meta.Tactic.bv.epr] quantified fact [2, 0] : ∀ (x : α) (y : β), R x y → Q y ∨ y = b₁
  [Meta.Tactic.bv.epr] quantified fact [0] : ∀ (y : β), Q y ↔ y = b₂
-/
#guard_msgs (trace, drop warning) in
example (α : Type) (β : Type 1) (a : α) (b₁ b₂ : β) (f : β → β) (R : α → β → Prop) (Q : β → Prop)
    (h1 : ∀ x y, R x y → Q y ∨ y = b₁) (h2 : ∀ y, Q y ↔ y = b₂) (h3 : ∀ y, ∃ x, R x y)
    (h4 : Q (f b₁) ↔ False) : R a b₁ ∨ b₁ = b₂ := by
  bv_normalize +epr
  sorry

section Unsat

variable (α : Type) (a b c : α) (P Q : α → Prop) (R : α → α → Prop) (q : Prop)

example (h1 : a = b) (h2 : b = c) (h3 : P a) (h4 : ¬P c) : False := by
  bv_decide +epr +uf

example (h1 : ∀ x y : α, x = y) (h2 : a ≠ b) : False := by
  bv_decide +epr +uf

example (h1 : ∀ x, P x ↔ q) (h2 : P a) (h3 : ¬P b) : False := by
  bv_decide +epr +uf

example (h1 : ∀ x y, R x y → R y x) (h2 : ∀ x y z, R x y → R y z → R x z) (h3 : R a b)
    (h4 : R b c) (h5 : ¬R c a) : False := by
  bv_decide +epr +uf

-- "Who killed Aunt Agatha?", TPTP problem `PUZ001`.
example [Nonempty α] (agatha butler charles : α) (lives : α → Prop)
    (killed richer hates : α → α → Prop)
    (h1 : lives agatha) (h2 : lives butler) (h3 : lives charles)
    (h4 : ∀ x y, ¬killed x y ∨ ¬richer x y)
    (h5 : ∀ x, ¬hates agatha x ∨ ¬hates charles x)
    (h6 : ∀ x, ¬hates x agatha ∨ ¬hates x butler ∨ ¬hates x charles)
    (h7 : hates agatha agatha) (h8 : hates agatha charles)
    (h9 : ∀ x y, ¬killed x y ∨ hates x y)
    (h10 : ∀ x, ¬hates agatha x ∨ hates butler x)
    (h11 : ∀ x, ¬lives x ∨ richer x agatha ∨ hates butler x)
    (h12 : killed butler agatha ∨ killed charles agatha) : False := by
  bv_decide +epr +uf

end Unsat

section Sat

/--
error: The prover found a counterexample, consider the following assignment:
R a b₁ = False
a = α₀
b₁ = β₀
b₂ = β₁
Q b₁ = False
Q b₂ = True
-/
#guard_msgs in
example (α : Type) (β : Type 1) (a : α) (b₁ b₂ : β) (R : α → β → Prop) (Q : β → Prop)
    (h1 : ∀ x y, R x y → Q y ∨ y = b₁) (h2 : ∀ y, Q y ↔ y = b₂) : R a b₁ ∨ b₁ = b₂ := by
  bv_decide +epr +uf

-- `h1` bounds the domain to `{a, b}`.
/--
error: The prover found a counterexample, consider the following assignment:
P b = False
b = α₁
P c = True
c = α₀
a = α₀
-/
#guard_msgs in
example (α : Type) (a b c : α) (P : α → Prop) (h1 : ∀ x, x = a ∨ x = b) (h2 : P b ≠ P c) :
    False := by
  bv_decide +epr +uf

end Sat
