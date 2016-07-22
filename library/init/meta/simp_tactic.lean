/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
open list nat

/- Simplify the given expression using [simp] and [congr] lemmas.
   The result is the simplified expression along with a proof that the new
   expression is equivalent to the old one.
   Fails if no simplifications can be performed.
   The first argument is a list of additional expressions to be considered as simp rules.
   The second argument is a tactic to be used to discharge proof obligations. -/
meta_constant simplify_core : list expr → tactic unit → expr → tactic (expr × expr)

meta_definition simp_core (rules : list expr) (prove_fn : tactic unit) : tactic unit :=
do (new_target, Heq) ← target >>= simplify_core rules prove_fn,
   assert "Htarget" new_target, swap,
   ns ← return (if expr.is_eq Heq ≠ none then "eq" else "iff" : name),
   Ht ← get_local "Htarget",
   mk_app (ns <.> "mpr") [Heq, Ht] >>= exact

meta_definition simp : tactic unit :=
simp_core [] failed >> try triv

meta_definition simp_using (Hs : list expr) : tactic unit :=
simp_core Hs failed >> try triv

private meta_definition is_equation : expr → bool
| (expr.pi _ _ _ b) := is_equation b
| e                 := match expr.is_eq e with some _ := tt | none := ff end

private meta_definition collect_eqs : list expr → tactic (list expr)
| []        := return []
| (H :: Hs) := do
  Eqs   ← collect_eqs Hs,
  Htype ← infer_type H >>= whnf,
  return $ if is_equation Htype = tt then H :: Eqs else Eqs

/- Simplify target using all hypotheses in the local context. -/
meta_definition simp_using_hs : tactic unit :=
local_context >>= collect_eqs >>= simp_using

meta_definition simp_core_at (rules : list expr) (prove_fn : tactic unit) (H : expr) : tactic unit :=
do when (expr.is_local_constant H = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   Htype ← infer_type H,
   (new_Htype, Heq) ← simplify_core rules prove_fn Htype,
   assert (expr.local_pp_name H) new_Htype,
   ns ← return (if expr.is_eq Heq ≠ none then "eq" else "iff" : name),
   mk_app (ns <.> "mp") [Heq, H] >>= exact,
   try $ clear H

meta_definition simp_at : expr → tactic unit :=
simp_core_at [] failed

meta_definition simp_at_using (Hs : list expr) : expr → tactic unit :=
simp_core_at Hs failed

meta_definition simp_at_using_hs (H : expr) : tactic unit :=
do Hs ← local_context >>= collect_eqs,
   simp_core_at (filter (ne H) Hs) failed H

meta_definition mk_eq_simp_ext (simp_ext : expr → tactic (expr × expr)) : tactic unit :=
do (lhs, rhs)     ← target >>= match_eq,
   (new_rhs, Heq) ← simp_ext lhs,
   unify rhs new_rhs,
   exact Heq

end tactic
