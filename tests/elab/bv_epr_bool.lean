import Std.Tactic.BVDecide

/-!
Tests for mixing `Prop` and `Bool` substructure in EPR problems.
-/

example {α : Type} [DecidableEq α] (a b c : α) (h1 : ∀ x, x = a || x = b) (h2 : c ≠ a) (h3 : c ≠ b) : False := by
  bv_decide +epr +uf

example {α : Type} [DecidableEq α] (a b c : α) (h1 : ∀ x, (!x = a) || (x = b)) (h2 : a = c) (h3 : c ≠ b) : False := by
  bv_decide +epr +uf

example {α : Type} [DecidableEq α] (a b c : α) (h1 : ∀ x, !x = a || (x = a ∧ x = b)) (h2 : a = c) (h3 : c ≠ b) : False := by
  bv_decide +epr +uf

example {α : Type} (a b : α) (p : α → Bool) (h1 : ∀ x, x = a → p x) (h2 : ¬p a) : False := by
  bv_decide +epr +uf

example {α : Type} (a b : α) (p : α → Bool) (h1 : ∀ x, x = a → p x) (h2 : !p a) : False := by
  bv_decide +epr +uf

/--
error: The prover found a counterexample, consider the following assignment:
p a = true
a = α₀
q a = True
-/
#guard_msgs in
example {α : Type} (a : α) (p : α → Bool) (q : α → Prop) (h1 : ∀ x, x = a → p x) (h2 : p a)
    (h3 : q a) : False := by
  bv_decide +epr +uf

-- Agatha puzzle with bool predicates
example {α : Type} [Nonempty α] (agatha butler charles : α) (lives : α → Bool)
    (killed richer hates : α → α → Bool)
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

-- Agatha puzzle with bool predicates + boolean substructure
example {α : Type} [Nonempty α] (agatha butler charles : α) (lives : α → Bool)
    (killed richer hates : α → α → Bool)
    (h1 : lives agatha) (h2 : lives butler) (h3 : lives charles)
    (h4 : ∀ x y, !killed x y || !richer x y)
    (h5 : ∀ x, ¬hates agatha x ∨ ¬hates charles x)
    (h6 : ∀ x, ¬hates x agatha ∨ !hates x butler ∨ !hates x charles)
    (h7 : hates agatha agatha) (h8 : hates agatha charles)
    (h9 : ∀ x y, !killed x y ∨ hates x y)
    (h10 : ∀ x, !hates agatha x || hates butler x)
    (h11 : ∀ x, ¬lives x ∨ richer x agatha ∨ hates butler x)
    (h12 : killed butler agatha ∨ killed charles agatha) : False := by
  bv_decide +epr +uf

example {α : Type} [DecidableEq α] (a b c : α) (h1 : ∀ x, if x = a then x = b else x = c) (h2 : a = c) (h3 : c ≠ b) : False := by
  bv_decide +epr +uf
