example (k : Prop)  (h : k) [Decidable k] (h' : c = 1) :
    let ⟨a, _⟩ := if k then (1, 0) else (0, 1)
    a = c := by
  simp [h]
  guard_target =ₛ 1 = c
  rw [h']
