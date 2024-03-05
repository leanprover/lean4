-- This is a preliminary list of aspirational goals for the new `auto` tactic.
-- I'm still trying to get a sense of the planned scope;
-- some of these may be quickly ruled out of scope!

macro "auto" : tactic => `(tactic| sorry)

namespace Nat

-- Nat.lt_asymm
example {a b : Nat} (h : a < b) : ¬ b < a :=
  Nat.not_lt.2 (Nat.le_of_lt h)
  -- If `Nat.not_lt : ¬a < b ↔ b ≤ a` is a `simp` rule,
  -- and `Nat.le_of_lt : a < b → a ≤ b` is a `have` rule:
  -- by auto

-- Nat.lt_iff_le_not_le
example {m n : Nat} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
  ⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun ⟨_, h⟩ => Nat.lt_of_not_ge h⟩
  -- Is proving `↔` via the constructor in scope? I presume so?
  -- If `Nat.not_le_of_gt : a < b → ¬b ≤ a` is an `apply` rule,
  -- and `Nat.not_le` is a `simp` rule:
  -- by auto

-- Nat.ne_iff_lt_or_gt
example {a b : Nat} : a ≠ b ↔ a < b ∨ b < a :=
  ⟨Nat.lt_or_gt_of_ne, fun | .inl h => Nat.ne_of_lt h | .inr h => Nat.ne_of_gt h⟩
  -- `Nat.lt_or_gt_of_ne : a ≠ b → a < b ∨ b < a` would be a `have` rule?
  -- We'll do cases on `Or`
  -- `Nat.ne_of_lt` and `Nat.ne_of_gt` would be `have` rules?

example (b : List α) (p : α → Prop) (h₁ : ∀ a ∈ b, p a) (h₂ : ∃ a ∈ b, ¬p a) : False :=
  by auto

-- From `Nat.ne_zero_implies_bit_true`
example {x : Nat}
    {hyp : x > 0 → x / 2 ≠ 0 → ∃ i, testBit (x / 2) i = true}
    {xnz : 2 * (x / 2) ≠ 0}
    {x_pos : x > 0} : ∃ i, testBit x i = true := by
  -- Is this in scope? Much harder. One has to:
  -- Deduce from `xnz` that `x / 2 ≠ 0`,
  -- Fill in the arguments of `hyp`,
  -- Realise, in the opposite direction of the `simp` lemma `testBit_succ`,
  -- that it is profitable to replace `testBit (x / 2) i` with `testBit x (i + 1)`.
  -- Instantiate the existential with `i + 1`.
  simp only [ne_eq, Nat.mul_eq_zero, Nat.add_zero, false_or] at xnz
  have ⟨d, dif⟩ := hyp x_pos xnz
  apply Exists.intro (d+1)
  simp_all only [gt_iff_lt, ne_eq, not_false_eq_true, forall_const, testBit_succ]

-- From `Nat.testBit_two_pow_sub_succ`
example (h : x < 2 ^ (n + 1)) :
    decide ((2 ^ (n + 1) - (x + 1)) % 2 = 1) =
      (decide (0 < n + 1) && !decide (x % 2 = 1)) := by
  -- "just logic and omega":
  simp only [zero_lt_succ, decide_True, Bool.true_and]
  rw [← decide_not, decide_eq_decide]
  omega
