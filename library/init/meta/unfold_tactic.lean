/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.relation_tactics init.meta.occurrences

namespace tactic
/- (rewrite_core m use_instances occs symm H) -/
meta constant unfold_expr_core : bool → occurrences → list name → expr → tactic expr

meta definition unfold_core (force : bool) (occs : occurrences) (ns : list name) : tactic unit :=
target >>= unfold_expr_core force occs ns >>= change

meta definition unfold : list name → tactic unit :=
unfold_core ff occurrences.all

meta definition unfold_occs_of (occs : list nat) (c : name) : tactic unit :=
unfold_core ff (occurrences.pos occs) [c]

meta definition unfold_core_at (force : bool) (occs : occurrences) (ns : list name) (H : expr) : tactic unit :=
do num_reverted : ℕ ← revert H,
   (expr.pi n bi d b : expr) ← target | failed,
   new_H : expr ← unfold_expr_core force occs ns d,
   change $ expr.pi n bi new_H b,
   intron num_reverted

meta definition unfold_at : list name → expr → tactic unit :=
unfold_core_at ff occurrences.all

end tactic
