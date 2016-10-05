/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open expr

private meta def relation_tactic (op_for : environment → name → option name) (tac_name : string) : tactic unit :=
do tgt ← target,
   env ← get_env,
   r   ← return $ get_app_fn tgt,
   match (op_for env (const_name r)) with
   | (some refl) := mk_const refl >>= apply
   | none        := fail $ tac_name ++ " tactic failed, target is not a relation application with the expected property."
   end

meta def reflexivity : tactic unit :=
relation_tactic environment.refl_for "reflexivity"

meta def symmetry : tactic unit :=
relation_tactic environment.symm_for "symmetry"

meta def transitivity : tactic unit :=
relation_tactic environment.trans_for "transitivity"

meta def relation_lhs_rhs : expr → tactic (name × expr × expr) :=
λ e, do
  (const c _) ← return e^.get_app_fn | failed,
  env ← get_env,
  (some (arity, lhs_pos, rhs_pos)) ← return $ env^.relation_info c | failed,
  args ← return $ get_app_args e,
  guard (args^.length = arity),
  (some lhs) ← return $ args^.nth lhs_pos | failed,
  (some rhs) ← return $ args^.nth rhs_pos | failed,
  return (c, lhs, rhs)

meta def target_lhs_rhs : tactic (name × expr × expr) :=
target >>= relation_lhs_rhs

end tactic
