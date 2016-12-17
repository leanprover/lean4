/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .prover_state
open monad expr list tactic

namespace super

private meta def find_components : list expr → list (list (expr × ℕ)) → list (list (expr × ℕ))
| (e::es) comps :=
  let (contain_e, do_not_contain_e) :=
      partition (λc : list (expr × ℕ), c^.exists_ $ λf,
        (abstract_local f.1 e^.local_uniq_name)^.has_var) comps in
    find_components es $ list.join contain_e :: do_not_contain_e
| _ comps := comps

meta def get_components (hs : list expr) : list (list expr) :=
(find_components hs (hs^.zip_with_index^.for $ λh, [h]))^.for $ λc,
(sort_on (λh : expr × ℕ, h.2) c)^.for $ λh, h.1

meta def extract_assertions : clause → prover (clause × list expr) | c :=
if c^.num_lits = 0 then return (c, [])
else if c^.num_quants ≠ 0 then do
  qf ← ♯ c^.open_constn c^.num_quants,
  qf_wo_as ← extract_assertions qf.1,
  return (qf_wo_as.1^.close_constn qf.2, qf_wo_as.2)
else do
  hd ← return $ c^.get_lit 0,
  hyp_opt ← get_sat_hyp_core hd^.formula hd^.is_neg,
  match hyp_opt with
  | some h := do
      wo_as ← extract_assertions (c^.inst h),
      return (wo_as.1, h :: wo_as.2)
  | _ := do
      op ← ♯c^.open_const,
      op_wo_as ← extract_assertions op.1,
      return (op_wo_as.1^.close_const op.2, op_wo_as.2)
  end

meta def mk_splitting_clause' (empty_clause : clause) : list (list expr) → tactic (list expr × expr)
| [] := return ([], empty_clause^.proof)
| ([p] :: comps) := do p' ← mk_splitting_clause' comps, return (p::p'.1, p'.2)
| (comp :: comps) := do
  (hs, p') ← mk_splitting_clause' comps,
  hnc ← mk_local_def `hnc (imp (pis comp empty_clause^.local_false) empty_clause^.local_false),
  p'' ← return $ app hnc (lambdas comp p'),
  return (hnc::hs, p'')

meta def mk_splitting_clause (empty_clause : clause) (comps : list (list expr)) : tactic clause := do
(hs, p) ← mk_splitting_clause' empty_clause comps,
return $ { empty_clause with proof := p }^.close_constn hs

@[super.inf]
meta def splitting_inf : inf_decl := inf_decl.mk 30 $ take given, do
lf ← flip monad.lift state_t.read $ λst, st^.local_false,
op ← ♯ given^.c^.open_constn given^.c^.num_binders,
if list.bor (given^.c^.get_lits^.for $ λl, (is_local_not lf l^.formula)^.is_some) then return () else
let comps := get_components op.2 in
if comps^.length < 2 then return () else do
splitting_clause ← ♯ mk_splitting_clause op.1 comps,
ass ← collect_ass_hyps splitting_clause,
add_sat_clause (splitting_clause^.close_constn ass) given^.sc^.sched_default,
remove_redundant given^.id []

end super
