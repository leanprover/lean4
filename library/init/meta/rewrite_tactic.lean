/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.relation_tactics

namespace tactic
/- (rewrite_core m use_instances occs symm H) -/
meta_constant rewrite_core : transparency → bool → option (list nat) → bool → expr → tactic unit
meta_constant rewrite_at_core : transparency → bool → option (list nat) → bool → expr → expr → tactic unit

meta_definition rewrite (th_name : name) : tactic unit :=
do th ← mk_const th_name,
   rewrite_core reducible tt none ff th,
   try reflexivity

meta_definition rewrite_at (th_name : name) (H_name : name) : tactic unit :=
do th ← mk_const th_name,
   H  ← get_local H_name,
   rewrite_at_core reducible tt none ff th H

end tactic
