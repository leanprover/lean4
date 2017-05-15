/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .clausifier .cdcl_solver
open tactic expr monad super

meta def cdcl_t (th_solver : tactic unit) : tactic unit := do
as_refutation, local_false ← target,
clauses ← clauses_of_context, clauses ← get_clauses_classical clauses,
for clauses (λc, do c_pp ← pp c, clause.validate c <|> fail c_pp),
res ← cdcl.solve (cdcl.theory_solver_of_tactic th_solver) local_false clauses,
match res with
| (cdcl.result.unsat proof) := exact proof
| (cdcl.result.sat interp) :=
  let interp' := do e ← interp.to_list, [if e.2 = tt then e.1 else `(not %%e.1)] in
  do pp_interp ← pp interp',
     fail (to_fmt "satisfying assignment: " ++ pp_interp)
end

meta def cdcl : tactic unit := cdcl_t skip
