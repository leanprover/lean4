module
abbrev ℕ :=  Nat

def hyperoperation : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k + 1
  | 1, m, 0 => m
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | n + 1, m, k + 1 => hyperoperation n m (hyperoperation (n + 1) m k)

attribute [local grind] hyperoperation

@[grind =]
theorem hyperoperation_zero (m k : ℕ) : hyperoperation 0 m k = k + 1 := by
  grind

@[grind =]
theorem hyperoperation_recursion (n m k : ℕ) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  grind

@[grind =]
theorem hyperoperation_one (m k : ℕ) : hyperoperation 1 m k = m + k := by
  induction k with grind

@[grind =]
theorem hyperoperation_two (m k : ℕ) : hyperoperation 2 m k = m * k := by
  induction k with grind

@[grind =]
theorem hyperoperation_three (m k : ℕ) : hyperoperation 3 m k = m ^ k := by
  induction k with grind

@[grind =] theorem hyperoperation_ge_three_one (n k : ℕ) : hyperoperation (n + 3) 1 k = 1 := by
  induction n generalizing k with
  | zero => grind
  | succ n ih => cases k <;> grind
