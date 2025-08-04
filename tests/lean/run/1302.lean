-- Extra boiler plate
instance : NeZero (a :: as).length where
  out := by simp

@[simp] theorem get_cons_zero {as : List α} : (a :: as).get (0 : Fin ((a :: as).length)) = a := rfl

example (a b c : α) : [a, b, c].get ⟨0, by simp (config := { decide := true })⟩ = a := by
  simp

example (a : Bool) : (a :: as).get ⟨0, by simp +arith⟩ = a := by
  simp

example (a : Bool) : (a :: as).get ⟨0, by simp +arith⟩ = a := by
  simp

-- Need to change Fin.zero_eta.
theorem zero_eta [NeZero n] : (⟨0, h⟩ : Fin n) = 0 := rfl

example (a b c : α) : [a, b, c].get ⟨0, id <| by simp (config := { decide := true })⟩ = a := by
  rw [zero_eta, get_cons_zero]
