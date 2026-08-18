
example (p q : Prop) : p → q → p ∧ q := by
  sym =>
    intro hp hq
    apply And.intro
    apply hp
    apply hq

register_sym_simp chainSimp where
  post := ground >> rewrite [Nat.add_zero, Nat.zero_add]

example (x y : Nat) (h : x ≤ y) : (1 - 1) + x  ≤ y + (1 + 0) := by
  sym =>
    simp chainSimp
    -- In the following tactic the goal is closed while preprocessing the target
    lia

example : ∃ x, x = a := by
  sym =>
    apply Exists.intro
    apply Eq.refl
