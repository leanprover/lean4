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

-- A simple logic puzzle: extract a witness from `h₂`, specialize `h₁` at it.
example (b : List α) (p : α → Prop) (h₁ : ∀ a ∈ b, p a) (h₂ : ∃ a ∈ b, ¬p a) : False :=
  by auto

-- From `Nat.testBit_two_pow_sub_succ`
example (h : x < 2 ^ (n + 1)) :
    decide ((2 ^ (n + 1) - (x + 1)) % 2 = 1) =
      (decide (0 < n + 1) && !decide (x % 2 = 1)) := by
  -- "just logic and omega":
  simp only [zero_lt_succ, decide_True, Bool.true_and]
  rw [← decide_not, decide_eq_decide]
  omega

-- From `Nat.ne_zero_implies_bit_true`
example {x : Nat}
    {hyp : x > 0 → x / 2 ≠ 0 → ∃ i, testBit (x / 2) i = true}
    {xnz : 2 * (x / 2) ≠ 0}
    {x_pos : x > 0} : ∃ i, testBit x i = true := by
  -- Is this in scope? Much harder. One has to:
  -- * Realise that in `hyp` we could replace `testBit (x / 2) i` with `testBit x (i + 1)`.
  --   (this is the simp lemma `testBit_succ` in the opposite direction)
  -- * Now see that `hyp` could be used to instantiate the existential with `i + 1`.
  -- * After that, deduce `x / 2 ≠ 0` from `xnz`.
  simp only [ne_eq, Nat.mul_eq_zero, Nat.add_zero, false_or] at xnz
  have ⟨d, dif⟩ := hyp x_pos xnz
  apply Exists.intro (d+1)
  simp_all only [gt_iff_lt, ne_eq, not_false_eq_true, forall_const, testBit_succ]

end Nat

namespace List

-- From `List.mem_filter`
example : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  -- Is it even in scope to try induction?
  induction as with
  | nil => simp
  | cons a as ih =>
    /-
    The original proof proceeds here as:
    ```
    by_cases h : p a <;> simp [*, or_and_right]
    · exact or_congr_left (and_iff_left_of_imp fun | rfl => h).symm
    · exact (or_iff_right fun ⟨rfl, h'⟩ => h h').symm
    ```
    However it is not reasonable to get that one should use `by_cases p a` yet.
    -/
    -- It might be reasonable for `auto` to be aware of `filter_cons`,
    -- even though it is not a simp lemma.
    simp [filter_cons]
    -- Now it is reasonable to split:
    split
    · simp [*]
      sorry -- just logic from here
    · simp [*]
      sorry -- just slightly trickier logic from here


-- Recall:
-- theorem append_inj :
--     ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂

-- From `List.append_inj'`
example (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  -- It seems unreasonable for `append_inj` to be a global `apply` rule,
  -- but it could be added local, or might be reasonable as a `have` rule.
  -- In either case, after using it,
  -- `auto` would need to deduce `s₁.length = s₂.length` from `hl`.
  -- If `auto` can apply `List.length` to `h`, then after simplifying this is just arithmetic.
  auto
  -- Original proof:
  -- append_inj h <| @Nat.add_right_cancel _ (length t₁) _ <| by
  -- let hap := congrArg length h; simp only [length_append, ← hl] at hap; exact hap



end List
