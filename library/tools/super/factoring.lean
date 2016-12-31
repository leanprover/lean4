/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .prover_state .subsumption
open tactic expr monad

namespace super

variable gt : expr → expr → bool

meta def inst_lit (c : clause) (i : nat) (e : expr) : tactic clause := do
opened ← clause.open_constn c i,
return $ clause.close_constn (clause.inst opened.1 e) opened.2

private meta def try_factor' (c : clause) (i j : nat) : tactic clause := do
qf ← clause.open_metan c c^.num_quants,
unify_lit (qf.1^.get_lit i) (qf.1^.get_lit j),
qfi ← clause.inst_mvars qf.1,
guard $ clause.is_maximal gt qfi i,
at_j ← clause.open_constn qf.1 j,
hyp_i ← option.to_monad (list.nth at_j.2 i),
clause.meta_closure qf.2 $ (at_j.1^.inst hyp_i)^.close_constn at_j.2

meta def try_factor (c : clause) (i j : nat) : tactic clause :=
if i > j then try_factor' gt c j i else try_factor' gt c i j

meta def try_infer_factor (c : derived_clause) (i j : nat) : prover unit := do
f  ← try_factor gt c^.c i j,
ss ← does_subsume f c^.c,
if ss then do
  f ← mk_derived f c^.sc^.sched_now,
  add_inferred f,
  remove_redundant c^.id [f]
else do
  inf_score 1 [c^.sc] >>= mk_derived f >>= add_inferred

@[super.inf]
meta def factor_inf : inf_decl := inf_decl.mk 40 $
take given, do gt ← get_term_order, sequence' $ do
  i ← given^.selected,
  j ← list.range given^.c^.num_lits,
  return $ try_infer_factor gt given i j <|> return ()

meta def factor_dup_lits_pre := preprocessing_rule $ take new, do
for new $ λdc, do
  dist ← dc^.c^.distinct,
  return { dc with c := dist }

end super
