/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open expr

private meta def relation_tactic (md : transparency) (op_for : environment → name → option name) (tac_name : string) : tactic unit :=
do tgt   ← target >>= instantiate_mvars,
   env   ← get_env,
   let r := get_app_fn tgt,
   match (op_for env (const_name r)) with
   | (some refl) := do r ← mk_const refl, apply_core r {md := md, new_goals := new_goals.non_dep_only} >> return ()
   | none        := fail $ tac_name ++ " tactic failed, target is not a relation application with the expected property."
   end

meta def reflexivity (md := semireducible) : tactic unit :=
relation_tactic md environment.refl_for "reflexivity"

meta def symmetry (md := semireducible) : tactic unit :=
relation_tactic md environment.symm_for "symmetry"

meta def transitivity (md := semireducible) : tactic unit :=
relation_tactic md environment.trans_for "transitivity"

meta def relation_lhs_rhs (e : expr) : tactic (name × expr × expr) :=
do (const c _) ← return e.get_app_fn,
   env ← get_env,
   (some (arity, lhs_pos, rhs_pos)) ← return $ env.relation_info c,
   args ← return $ get_app_args e,
   guard (args.length = arity),
   (some lhs) ← return $ args.nth lhs_pos,
   (some rhs) ← return $ args.nth rhs_pos,
   return (c, lhs, rhs)

meta def target_lhs_rhs : tactic (name × expr × expr) :=
target >>= relation_lhs_rhs

/-- Try to apply subst exhaustively -/
meta def subst_vars : tactic unit :=
focus1 $ iterate (any_hyp subst) >> try (reflexivity reducible)

end tactic
