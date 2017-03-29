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
-- instantiate universal quantifiers using meta-variables
(qf, mvars) ← c.open_metan c.num_quants,
-- unify the two literals
unify_lit (qf.get_lit i) (qf.get_lit j),
-- check maximality condition
qfi ← qf.inst_mvars, guard $ clause.is_maximal gt qfi i,
-- construct proof
(at_j, cs) ← qf.open_constn j, hyp_i ← cs.nth i,
let qf' := (at_j.inst hyp_i).close_constn cs,
-- instantiate meta-variables and replace remaining meta-variables by quantifiers
clause.meta_closure mvars qf'

meta def try_factor (c : clause) (i j : nat) : tactic clause :=
if i > j then try_factor' gt c j i else try_factor' gt c i j

meta def try_infer_factor (c : derived_clause) (i j : nat) : prover unit := do
f  ← try_factor gt c.c i j,
ss ← does_subsume f c.c,
if ss then do
  f ← mk_derived f c.sc.sched_now,
  add_inferred f,
  remove_redundant c.id [f]
else do
  inf_score 1 [c.sc] >>= mk_derived f >>= add_inferred

@[super.inf]
meta def factor_inf : inf_decl := inf_decl.mk 40 $
take given, do gt ← get_term_order, sequence' $ do
  i ← given.selected,
  j ← list.range given.c.num_lits,
  return $ try_infer_factor gt given i j <|> return ()

meta def factor_dup_lits_pre := preprocessing_rule $ take new, do
for new $ λdc, do
  dist ← dc.c.distinct,
  return { dc with c := dist }

end super
