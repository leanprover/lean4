/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
/- Simplify the given expression using [defeq] lemmas.
   The resulting expression is definitionally equal to the input. -/
meta constant defeq_simp_core : transparency → expr → tactic expr

meta def defeq_simp : expr → tactic expr :=
defeq_simp_core reducible

meta def dsimp : tactic unit :=
target >>= defeq_simp >>= change

meta def dsimp_at (H : expr) : tactic unit :=
do num_reverted : ℕ ← revert H,
   (expr.pi n bi d b : expr) ← target | failed,
   H_simp : expr ← defeq_simp d,
   change $ expr.pi n bi H_simp b,
   intron num_reverted

end tactic
