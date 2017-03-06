/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .prover_state
open expr list monad

namespace super

meta def is_taut (c : clause) : tactic bool := do
qf ← c^.open_constn c^.num_quants,
return $ list.bor $ do
  l1 ← qf^.1^.get_lits, guard l1^.is_neg,
  l2 ← qf^.1^.get_lits, guard l2^.is_pos,
  [decidable.to_bool $ l1^.formula = l2^.formula]

meta def tautology_removal_pre : prover unit :=
preprocessing_rule $ λnew, filter (λc, lift bnot $ is_taut c^.c) new

meta def remove_duplicates : list derived_clause → list derived_clause
| [] := []
| (c :: cs) :=
  let (same_type, other_type) := partition (λc' : derived_clause, c'^.c^.type = c^.c^.type) cs in
  { c with sc := foldl score.min c^.sc (same_type^.map $ λc, c^.sc) } :: remove_duplicates other_type

meta def remove_duplicates_pre : prover unit :=
preprocessing_rule $ λnew,
return $ remove_duplicates new

meta def clause_normalize_pre : prover unit :=
preprocessing_rule $ λnew, for new $ λdc,
do c' ← dc^.c^.normalize, return { dc with c := c' }

end super
