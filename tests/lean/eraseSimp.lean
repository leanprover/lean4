theorem foo (n : Nat) : n + n = 2*n := by
  rw [Nat.mul_comm, Nat.mul_succ, Nat.mul_succ, Nat.mul_zero, Nat.zero_add]

attribute [-simp] foo -- Error

theorem ex1 {a b : Nat} (h₁ : a = b) : 0 + a = b := by
  simp
  assumption

section

attribute [-simp] Nat.zero_add

theorem ex2 {a b : Nat} (h₁ : a = b) : 0 + a = b := by
  fail_if_success simp -- did not apply `Nat.zero_add`
  rw [Nat.zero_add]
  assumption

end
-- Effect of the attribute command above is gone

theorem ex3 {a b : Nat} (h₁ : a = b) : 0 + a = b := by
  simp
  assumption

theorem ex4 {a b : Nat} (h₁ : a = b) : 0 + a = b := by
  fail_if_success simp [-Nat.zero_add]
  rw [Nat.zero_add]
  assumption
