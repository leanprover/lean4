/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open expr

private meta definition relation_tactic (op_for : environment → name → option name) (tac_name : string) : tactic unit :=
do tgt ← target,
   env ← get_env,
   r   ← return $ get_app_fn tgt,
   match (op_for env (const_name r)) with
   | (some refl) := mk_const refl >>= apply
   | none        := fail $ tac_name ++ " tactic failed, target is not a relation application with the expected property."
   end

meta definition reflexivity : tactic unit :=
relation_tactic environment.refl_for "reflexivity"

meta definition symmetry : tactic unit :=
relation_tactic environment.symm_for "symmetry"

meta definition transitivity : tactic unit :=
relation_tactic environment.trans_for "transitivity"

end tactic
