example (h₁: m < n) (h₂: m.succ.pred < n) :
  (Fin.mk m h₁).succ = (Fin.mk m.succ.pred h₂).succ := by
  simp
