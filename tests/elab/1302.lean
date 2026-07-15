@[simp] theorem get_cons_zero {as : List α} : (a :: as).get (0 : Fin (as.length + 1)) = a := rfl

example (a b c : α) : [a, b, c].get ⟨0, by simp (config := { decide := true })⟩ = a := by
  simp

example (a : Bool) : (a :: as).get ⟨0, by simp +arith⟩ = a := by
  simp

example (a : Bool) : (a :: as).get ⟨0, by simp +arith⟩ = a := by
  simp

example (a b c : α) : [a, b, c].get ⟨0, by simp (config := { decide := true })⟩ = a := by
  erw [Fin.zero_eta]
  rw [get_cons_zero]

example (a b c : α) : [a, b, c].get ⟨0, by simp (config := { decide := true })⟩ = a := by
  rw [List.get]
