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

axiom a5868 : Nat
axiom b5868 : Nat
axiom a5868_eq_b5868 : a5868 = b5868

axiom P5868 : Nat → Nat → Prop
@[simp] axiom P5868_b : P5868 b5868 b5868

attribute [simp] a5868_eq_b5868

example : P5868 a5868 b5868 := by simp

attribute [-simp] a5868_eq_b5868

/-- error: `simp` made no progress -/
#guard_msgs (error) in
example : P5868 a5868 b5868 := by simp

attribute [simp] a5868_eq_b5868

example : P5868 a5868 b5868 := by simp
