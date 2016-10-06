/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.relation_tactics init.meta.occurrences

namespace tactic
/- (rewrite_core m use_instances occs symm H) -/
meta constant rewrite_core : transparency → bool → occurrences → bool → expr → tactic unit
meta constant rewrite_at_core : transparency → bool → occurrences → bool → expr → expr → tactic unit

meta def rewrite (th_name : name) : tactic unit :=
do th ← mk_const th_name,
   rewrite_core reducible tt occurrences.all ff th,
   try reflexivity

meta def rewrite_at (th_name : name) (H_name : name) : tactic unit :=
do th ← mk_const th_name,
   H  ← get_local H_name,
   rewrite_at_core reducible tt occurrences.all ff th H

end tactic
