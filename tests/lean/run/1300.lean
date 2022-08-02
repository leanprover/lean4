set_option trace.Meta.debug true

example (hv : v < n) (ih: ∀ v : Fin n, ∃ v', v' ≤ v):
  True := by
  have ⟨w, hw⟩ := ih ⟨v, ‹_›⟩
  trivial
