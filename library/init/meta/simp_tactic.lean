/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
open list nat

meta constant simp_lemmas : Type

/- Create a data-structure containing a simp lemma for every constant in the first list of
   attributes, and a congr lemma for every constant in the second list of attributes.
   Lemmas with type `<lhs> <eqv_rel> <rhs>` are indexed using the head-symbol of `<lhs>`,
   computed with respect to the given transparency setting. -/
meta constant mk_simp_lemmas_core     : transparency → list name → list name → tactic simp_lemmas
/- Create an empty simp_lemmas. That is, it ignores the lemmas marked with the [simp] attribute.  -/
meta constant mk_empty_simp_lemmas     : tactic simp_lemmas
/- (simp_lemmas_insert_core m lemmas id lemma priority) adds the given lemma to the set simp_lemmas. -/
meta constant simp_lemmas_insert_core : transparency → simp_lemmas → expr → tactic simp_lemmas
/- Erase the given lemmas from the simp set. -/
meta constant simp_lemmas_erase       : simp_lemmas → list name → simp_lemmas

meta definition mk_simp_lemmas        : tactic simp_lemmas :=
mk_simp_lemmas_core reducible [`simp] [`congr]

meta definition simp_lemmas_add_extra : transparency → simp_lemmas → list expr → tactic simp_lemmas
| m sls []      := return sls
| m sls (l::ls) := do
  new_sls ← simp_lemmas_insert_core m sls l,
  simp_lemmas_add_extra m new_sls ls

/- Simplify the given expression using [simp] and [congr] lemmas.
   The first argument is a tactic to be used to discharge proof obligations.
   The second argument is the name of the relation to simplify over.
   The third argument is a list of additional expressions to be considered as simp rules.
   The fourth argument is the expression to be simplified.
   The result is the simplified expression along with a proof that the new
   expression is equivalent to the old one.
   Fails if no simplifications can be performed. -/
meta constant simplify_core : tactic unit → name → simp_lemmas → expr → tactic (expr × expr)

meta definition simplify (prove_fn : tactic unit) (extra_lemmas : list expr) (e : expr) : tactic (expr × expr) :=
do simp_lemmas  ← mk_simp_lemmas,
   new_lemmas   ← simp_lemmas_add_extra reducible simp_lemmas extra_lemmas,
   e_type       ← infer_type e >>= whnf,
   simplify_core prove_fn `eq new_lemmas e

meta definition simplify_goal (prove_fn : tactic unit) (extra_lemmas : list expr) : tactic unit :=
do (new_target, Heq) ← target >>= simplify prove_fn extra_lemmas,
   assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_app `eq.mpr [Heq, Ht] >>= exact

meta definition simp : tactic unit :=
simplify_goal failed [] >> try triv

meta definition simp_using (Hs : list expr) : tactic unit :=
simplify_goal failed Hs >> try triv

private meta definition is_equation : expr → bool
| (expr.pi n bi d b) := is_equation b
| e                  := match (expr.is_eq e) with (some a) := tt | none := ff end

private meta definition collect_eqs : list expr → tactic (list expr)
| []        := return []
| (H :: Hs) := do
  Eqs   ← collect_eqs Hs,
  Htype ← infer_type H >>= whnf,
  return $ if is_equation Htype then H :: Eqs else Eqs

/- Simplify target using all hypotheses in the local context. -/
meta definition simp_using_hs : tactic unit :=
local_context >>= collect_eqs >>= simp_using

meta definition simp_core_at (prove_fn : tactic unit) (extra_lemmas : list expr) (H : expr) : tactic unit :=
do when (expr.is_local_constant H = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   Htype ← infer_type H,
   (new_Htype, Heq) ← simplify prove_fn extra_lemmas Htype,
   assert (expr.local_pp_name H) new_Htype,
   mk_app `eq.mp [Heq, H] >>= exact,
   try $ clear H

meta definition simp_at : expr → tactic unit :=
simp_core_at failed []

meta definition simp_at_using (Hs : list expr) : expr → tactic unit :=
simp_core_at failed Hs

meta definition simp_at_using_hs (H : expr) : tactic unit :=
do Hs ← local_context >>= collect_eqs,
   simp_core_at failed (filter (ne H) Hs) H

meta definition mk_eq_simp_ext (simp_ext : expr → tactic (expr × expr)) : tactic unit :=
do (lhs, rhs)     ← target >>= match_eq,
   (new_rhs, Heq) ← simp_ext lhs,
   unify rhs new_rhs,
   exact Heq

end tactic
