namespace smt
open tactic

private meta_definition collect_props : list expr → tactic (list expr)
| []        := return []
| (H :: Hs) := do
  Eqs   ← collect_props Hs,
  Htype ← infer_type H >>= whnf,
  return $ if Htype = expr.prop then H :: Eqs else Eqs

meta_definition prove : tactic unit :=
do local_context >>= collect_props >>= revert_lst,
   simplify_goal failed []

end smt
