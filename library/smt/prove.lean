namespace smt
open tactic

private meta def collect_props : list expr → tactic (list expr)
| []        := return []
| (H :: Hs) := do
  Eqs   ← collect_props Hs,
  Htype ← infer_type H >>= whnf,
  return $ if Htype = expr.prop then (H :: Eqs) else Eqs

meta def prove : tactic unit :=
do local_context >>= collect_props >>= revert_lst,
   simp

end smt
