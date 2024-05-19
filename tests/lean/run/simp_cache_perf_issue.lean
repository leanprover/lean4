@[congr]
theorem exists_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    Exists q ↔ ∃ h : p', q' (hp.2 h) := sorry

set_option maxHeartbeats 1000 in
example (x : Nat) :
  ∃ (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x)
      (h : x = x), True := by
  simp only
  sorry
