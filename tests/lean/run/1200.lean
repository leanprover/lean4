example
(h: match .none (α:=α) with
| some _ => True
| _      => True):
  True := by
  split at h <;> trivial
