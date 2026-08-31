theorem ex1 : a * 2 = 2 * a := by
  have h : ∀ (a b : Nat), a * b = a * b := by
    intros; rfl
  conv at h =>
    intro a b; lhs; rw [Nat.mul_comm]
  exact h 2 a

#print ex1

theorem ex2 : a * 2 = 2 * a := by
  have h : (fun x y => x * y) = Nat.mul := by
    rfl
  conv at h =>
    lhs; intro x y; rw [Nat.mul_comm]
  exact congrFun (congrFun h 2) a

#print ex2
