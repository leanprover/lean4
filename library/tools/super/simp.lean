/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause_ops .prover_state
open tactic monad

namespace super

meta def prove_using_assumption : tactic unit := do
tgt ← target,
ass ← mk_local_def `h tgt,
exact ass

meta def simplify_capturing_assumptions (type : expr) : tactic (expr × expr × list expr) := do
S ← simp_lemmas.mk_default,
(type', heq) ← simplify default_simplify_config S type,
hyps ← return $ contained_lconsts type,
hyps' ← return $ contained_lconsts_list [type', heq],
add_hyps ← return $ list.filter (λn : expr, ¬hyps^.contains n^.local_uniq_name) hyps'^.values,
return (type', heq, add_hyps)

meta def try_simplify_left (c : clause) (i : ℕ) : tactic (list clause) :=
on_left_at c i $ λtype, do
  (type', heq, add_hyps) ← simplify_capturing_assumptions type,
  hyp ← mk_local_def `h type',
  prf  ← mk_app ``eq.mpr [heq, hyp],
  return [(hyp::add_hyps, prf)]

meta def try_simplify_right (c : clause) (i : ℕ) : tactic (list clause) :=
on_right_at' c i $ λhyp, do
  (type', heq, add_hyps) ← simplify_capturing_assumptions hyp^.local_type,
  heqtype ← infer_type heq,
  heqsymm ← mk_app ``eq.symm [heq],
  prf  ← mk_app ``eq.mpr [heqsymm, hyp],
  return [(add_hyps, prf)]

meta def simp_inf : inf_decl := inf_decl.mk 40 $ take given, sequence' $ do
r ← [try_simplify_right, try_simplify_left],
i ← list.range given^.c^.num_lits,
[inf_if_successful 2 given (r given^.c i)]

end super
