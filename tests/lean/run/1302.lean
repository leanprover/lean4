@[simp] theorem get_cons_zero {as : List α} : (a :: as).get ⟨0, Nat.zero_lt_succ _⟩ = a := rfl

example (a b c : α) : [a, b, c].get ⟨0, by simp (config := { decide := true })⟩ = a := by
  simp

example (a : Bool) : (a :: as).get ⟨0, by simp_arith⟩ = a := by
  simp

example (a : Bool) : (a :: as).get ⟨0, by simp_arith⟩ = a := by
  simp

example (a b c : α) : [a, b, c].get ⟨0, by simp (config := { decide := true })⟩ = a := by
  rw [get_cons_zero]
