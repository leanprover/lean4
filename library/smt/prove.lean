namespace smt
open tactic

private meta def collect_props : list expr → tactic (list expr)
| []        := return []
| (H :: Hs) := do
  Eqs   ← collect_props Hs,
  Htype ← infer_type H >>= infer_type >>= whnf,
  return $ if Htype = `(Prop) then (H :: Eqs) else Eqs

-- This tactic is just a placeholder, designed to be modified for specific performance experiments
meta def prove : tactic unit :=
do local_context >>= collect_props >>= revert_lst,
   trace "SMT state, after reverting propositions:",
   trace_state,
   `[simp { contextual := tt }]

end smt
