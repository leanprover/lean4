module

/-!
Tests that recognizing rational literals does not prevent arithmetic normalization of hypotheses
that resemble match conditions. A protected `1 / 2` pattern would remain disconnected from the
`2⁻¹` produced by normalizing an ordinary hypothesis, even when both hypotheses use `1 / 2`.
-/

set_option grind.debug true

example (a : Rat) (h : a = 1 / 2 → False) (ha : a = 1 / 2) : False := by
  grind

example (a : Rat) (h : a = 1 / 2 → False) (ha : 2 * a = 1) : False := by
  grind

example (a : Rat) (h : a = 2 / 4 → False) (ha : a = 1 / 2) : False := by
  grind

example (a : Rat) (h : a = -1 / 2 → False) (ha : 2 * a = -1) : False := by
  grind

example (a : Rat) (h : a = 0.5 → False) (ha : 2 * a = 1) : False := by
  grind

example (a : Rat) (h : a = -0.5 → False) (ha : 2 * a = -1) : False := by
  grind

example (a : Rat) (h : a = 1.0 / 2.0 → False) (ha : 2 * a = 1) : False := by
  grind

inductive Node where
  | mk : Nat → Rat → Node

example (v : Node) (h : ∀ n, v = Node.mk n (1 / 2) → False)
    (hv : v = Node.mk 0 (1 / 2)) : False := by
  grind

example (v : Node) (h : ∀ n, v = Node.mk n 0.5 → False)
    (hv : v = Node.mk 0 (1 / 2)) : False := by
  grind

example (a b : Rat) (h : ∀ n : Rat, a = n + 1 / 2 → False)
    (ha : a = b + 1 / 2) : False := by
  grind

example (a b : Rat) (h : ∀ n : Rat, a = n + 0.5 → False)
    (ha : a = b + 1 / 2) : False := by
  grind

example (p : Prop) (h : p = True → False) (hp : p) : False := by
  grind

example (p : Prop) (h : p = False → False) (hp : ¬p) : False := by
  grind
