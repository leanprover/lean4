open Nat

attribute [grind] testBit_eq_decide_div_mod_eq


theorem exists_ge_and_testBit_of_ge_two_pow {x : Nat} (p : x ≥ 2^n) : ∃ i ≥ n, testBit x i := by
  false_or_by_contra
  rename_i h
  simp at h
  grind
theorem eq_of_testBit_eq {x y : Nat} (pred : ∀i, testBit x i = testBit y i) : x = y := by
  grind
theorem exists_testBit_ne_of_ne {x y : Nat} (p : x ≠ y) : ∃ i, testBit x i ≠ testBit y i := by
  grind
theorem exists_testBit_of_ne_zero {x : Nat} (xnz : x ≠ 0) : ∃ i, testBit x i := by
  grind

example {a b : Nat}: b * (a / b) + a % b = a := by exact div_add_mod a b

grind_pattern div_add_mod => m % n
grind_pattern div_add_mod => m / n

example {x i : Nat} (h : x / 2 ^ i % 2 = 1) : x / 2 ^ i ≥ 1 := by grind
example {x i : Nat} (h : x / 2 ^ i % 2 = 1) : x ≥ 2 ^ i := by grind

example {a b c d : Nat} (h : a = b + c * d) (w : 1 ≤ d) : a ≥ c := by
  -- grind -- fails, but would be lovely
  subst h
  apply Nat.le_add_left_of_le
  apply Nat.le_mul_of_pos_right
  assumption

example {a b c d : Int} (h : a = b + c * d) (hb : 0 ≤ b) (hc : 0 ≤ c) (w : 1 ≤ d) : a ≥ c := by
  -- grind -- fails also
  subst h
  conv => rhs; rw [← Int.zero_add c]
  apply Int.add_le_add
  · assumption
  · have : 0 ≤ c * (d - 1) := Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_sub, Int.mul_one, Int.sub_nonneg] at this
    exact this

-- Note: if we can automate the `Int` version here, we can also automate the `Nat` version just by embedding in `Int`.

open Lean Grind

example {α : Type} [Lean.Grind.IntModule α] [Lean.Grind.Preorder α] [Lean.Grind.IntModule.IsOrdered α] {a b c : α} {d : Int}
    (wb : 0 ≤ b) (wc : 0 ≤ c)
    (h : a = b + d * c) (w : 1 ≤ d) : a ≥ c := by
  subst h
  conv => rhs; rw [← IntModule.zero_add c]
  apply IntModule.IsOrdered.add_le_add
  · exact wb
  · have := IntModule.IsOrdered.hmul_le_hmul_of_le_of_le_of_nonneg_of_nonneg w (Preorder.le_refl c) (by decide) wc
    rwa [IntModule.one_hmul] at this

-- We can prove this directly in an ordered NatModule, from the axioms. (But shouldn't, see below.)
example {α : Type} [Lean.Grind.NatModule α] [Lean.Grind.Preorder α] [Lean.Grind.NatModule.IsOrdered α] {a b c : α} {d : Nat}
    (wb : 0 ≤ b) (wc : 0 ≤ c)
    (h : a = b + d * c) (w : 1 ≤ d) : a ≥ c := by
  subst h
  conv => rhs; rw [← NatModule.zero_add c]
  apply NatModule.IsOrdered.add_le_add
  · exact wb
  · have := NatModule.IsOrdered.hmul_le_hmul_of_le_of_le_of_nonneg w (Preorder.le_refl c) wc
    rwa [NatModule.one_hmul] at this

-- The correct proof is to embed a NatModule in its IntModule envelope.

theorem ge_two_pow_of_testBit {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  have : 1 ≤ x / 2 ^ i := by grind?
  have := div_add_mod x (2 ^ i)
  have : 1 * 2 ^ i ≤ x := Nat.mul_le_of_le_div _ _ _ this
  grind
theorem testBit_lt_two_pow {x i : Nat} (lt : x < 2^i) : x.testBit i = false := by
  grind
theorem lt_pow_two_of_testBit (x : Nat) (p : ∀i, i ≥ n → testBit x i = false) : x < 2^n := by
  grind
theorem testBit_two_pow {n m : Nat} : testBit (2 ^ n) m = decide (n = m) := by
  grind
theorem le_of_testBit {n m : Nat} (h : ∀ i, n.testBit i = true → m.testBit i = true) : n ≤ m := by
  grind


theorem testBit_mul_two_pow (x i n : Nat) :
    (x * 2 ^ n).testBit i = (decide (n ≤ i) && x.testBit (i - n)) := by
  grind

theorem testBit_two_pow_mul_add (a : Nat) {b i : Nat} (b_lt : b < 2^i) (j : Nat) :
    testBit (2 ^ i * a + b) j =
      if j < i then
        testBit b j
      else
        testBit a (j - i) := by
  grind

theorem testBit_two_pow_mul :
    testBit (2 ^ i * a) j = (decide (j ≥ i) && testBit a (j-i)) := by
  grind
