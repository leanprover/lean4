example (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ (q ∧ (r ∧ p)) := by
  and_intros
  · exact hp
  · exact hq
  · exact hq
  · exact hr
  · exact hp
