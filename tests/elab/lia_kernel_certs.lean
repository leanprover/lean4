/-!
`lia` proofs whose certificates the kernel checks by evaluating the recursor-based (`_k`)
operations of `Init.Data.Int.Kernel` and `Init.Data.Int.Linear`. Each example exercises the
certificate named in its comment.
-/

-- `dvd_unsat`
example (x y : Int) (h₁ : 1 ≤ 3*x - 3*y) (h₂ : 3*x - 3*y ≤ 4) (h₃ : 3 ∣ x + 2*y + 6)
    (h₄ : 0 ≤ y) (h₅ : y ≤ 20) : False := by
  lia

-- `dvd_solve_elim`
example (x y : Int) (h₁ : 0 ≤ 4*x + 3*y) (h₂ : 4*x + 3*y ≤ 1) (h₃ : 6 ∣ 4*x - 3*y + 3)
    (h₄ : 0 ≤ y) (h₅ : y ≤ 5) : False := by
  lia

-- `cooper_dvd_left_split_dvd2`
example (x y : Int) (h₁ : 0 ≤ 7*x - 3*y) (h₂ : 7*x - 3*y ≤ 1) (h₃ : 5 ∣ 3*x - 3*y + 4)
    (h₄ : 0 ≤ y) (h₅ : y ≤ 5) : False := by
  lia

-- `cooper_dvd_right_split_dvd2`
example (x y : Int) (h₁ : -6 ≤ 7*x + y) (h₂ : 7*x + y ≤ -4) (h₃ : 7 ∣ 3*x - 3*y + 3)
    (h₄ : 0 ≤ y) (h₅ : y ≤ 10) : False := by
  lia

-- `eq_unsat_coeff`
example (x y z : Int) (h₁ : x = 2*y) (h₂ : x = 2*z + 1) : False := by
  lia

-- `mul_eq_kk`
example (x : Int) (h : x = -3) : x * x * x = -27 := by
  lia

-- `mul_eq_kkx`
example (x y z : Int) (h₁ : x = 3) (h₂ : y = 4*z) : x * y = 12*z := by
  lia

-- `mul_eq_kxk`
example (x y : Int) (h₁ : x = 3) (h₂ : y = 4) : x * y = 12 := by
  lia

-- `div_eq'`
example (y : Int) (h : y = 3) : 10 / y = 3 := by
  lia

example (y : Int) (h : y = -3) : -10 / y = 4 := by
  lia

-- `mod_eq'`
example (y : Int) (h : y = 3) : 10 % y = 1 := by
  lia

example (y : Int) (h : y = -3) : -10 % y = 2 := by
  lia

-- `pow_eq`
example (n : Nat) (h : n = 3) : (2 : Int) ^ n = 8 := by
  lia

example (x : Int) (n : Nat) (h₁ : x = -2) (h₂ : n = 3) : x ^ n = -8 := by
  lia

example (x : Int) (n : Nat) (h₁ : x = -2) (h₂ : n = 4) : x ^ n = 16 := by
  lia
