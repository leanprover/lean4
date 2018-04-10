meta def mk_local_pis : expr → tactic (list expr × expr)
| p := do
  (ps, r) ← mk_local_pis p,
  return ((p :: ps), r)
