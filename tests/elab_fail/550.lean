example (h : ∀ x, x + 1 = x.succ) : (x + 1) + 1 = 1 + (x + 1) := by
  rewrite [h]
  done
