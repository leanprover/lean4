#exit
-- import algebra.ordered_ring
open tactic
axiom Sorry : ∀ {A:Type}, A

example {A : Type} [ordered_ring A] (a b c : A) (h₀ : c > 0) (h₁ : a > 1) (h₂ : b > 0) : a + b + c = 0 :=
by do
  [x, y] ← match_target_subexpr `(λ x y : A, x + y) | failed,
  trace "------ subterms -------",
  trace x, trace y,
  (h, [z]) ← match_hypothesis `(λ x : A, x > 1) | failed,
  trace "--- hypothesis of the form x > 1 ---",
  trace h, trace z,
  refine `(Sorry)
