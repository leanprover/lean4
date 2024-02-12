example (hp : p) (hq : q) (hr : r) : (p ∧ q) ∧ (q ∧ (r ∧ p)) := by
  split_ands
  · exact hp
  · exact hq
  · exact hq
  · exact hr
  · exact hp
