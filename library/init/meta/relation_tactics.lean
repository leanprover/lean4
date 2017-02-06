/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open expr

private meta def relation_tactic (t : transparency) (op_for : environment → name → option name) (tac_name : string) : tactic unit :=
do tgt ← target,
   env ← get_env,
   r   ← return $ get_app_fn tgt,
   match (op_for env (const_name r)) with
   | (some refl) := mk_const refl >>= apply_core t tt ff tt
   | none        := fail $ tac_name ++ " tactic failed, target is not a relation application with the expected property."
   end

meta def reflexivity_core (t : transparency) : tactic unit :=
relation_tactic t environment.refl_for "reflexivity"

meta def reflexivity : tactic unit :=
reflexivity_core semireducible

meta def symmetry : tactic unit :=
relation_tactic semireducible environment.symm_for "symmetry"

meta def transitivity : tactic unit :=
relation_tactic semireducible environment.trans_for "transitivity"

meta def relation_lhs_rhs : expr → tactic (name × expr × expr) :=
λ e, do
  (const c _) ← return e^.get_app_fn,
  env ← get_env,
  (some (arity, lhs_pos, rhs_pos)) ← return $ env^.relation_info c,
  args ← return $ get_app_args e,
  guard (args^.length = arity),
  (some lhs) ← return $ args^.nth lhs_pos,
  (some rhs) ← return $ args^.nth rhs_pos,
  return (c, lhs, rhs)

meta def target_lhs_rhs : tactic (name × expr × expr) :=
target >>= relation_lhs_rhs

end tactic
