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


theorem ge_two_pow_of_testBit {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  have : 1 ≤ x / 2 ^ i := sorry
  have := Nat.mul_le_of_le_div _ _ _ this
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
