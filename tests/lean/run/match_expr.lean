open tactic
axiom Sorry : ∀ {A:PType*}, A

example (a b c : nat) (h₀ : c > 0) (h₁ : a > 1) (h₂ : b > 0) : a + b + c = 0 :=
by do
  [x, y] ← match_target_subexpr `(λ x y : nat, x + y) | failed,
  trace "------ subterms -------",
  trace x, trace y,
  (h, [z]) ← match_hypothesis `(λ x : nat, x > 1) | failed,
  trace "--- hypothesis of the form x > 1 ---",
  trace h, trace z,
  refine `(Sorry)
