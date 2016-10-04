/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics

meta constant simp_lemmas : Type
meta constant simp_lemmas.mk    : simp_lemmas
meta constant simp_lemmas.join  : simp_lemmas → simp_lemmas → simp_lemmas
meta constant simp_lemmas.erase : simp_lemmas → list name → simp_lemmas

namespace tactic
open list nat
/- Create a data-structure containing a simp lemma for every constant in the first list of
   attributes, and a congr lemma for every constant in the second list of attributes.
   Lemmas with type `<lhs> <eqv_rel> <rhs>` are indexed using the head-symbol of `<lhs>`,
   computed with respect to the given transparency setting. -/
meta constant mk_simp_lemmas_core     : transparency → list name → list name → tactic simp_lemmas
/- (simp_lemmas_insert_core m lemmas lemma priority) adds the given lemma to the set simp_lemmas. -/
meta constant simp_lemmas_insert_core : transparency → simp_lemmas → expr → tactic simp_lemmas
/- (simp_lemmas_insert_constant_core m lemmas cname) -/
meta constant simp_lemmas_insert_constant_core : transparency → simp_lemmas → name → tactic simp_lemmas

meta def simp_lemmas_insert_constant : simp_lemmas → name → tactic simp_lemmas :=
simp_lemmas_insert_constant_core reducible

meta def mk_simp_lemmas        : tactic simp_lemmas :=
mk_simp_lemmas_core reducible [`simp] [`congr]

meta def simp_lemmas_add_extra : transparency → simp_lemmas → list expr → tactic simp_lemmas
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

meta def simplify (prove_fn : tactic unit) (extra_lemmas : list expr) (e : expr) : tactic (expr × expr) :=
do simp_lemmas  ← mk_simp_lemmas,
   new_lemmas   ← simp_lemmas_add_extra reducible simp_lemmas extra_lemmas,
   e_type       ← infer_type e >>= whnf,
   simplify_core prove_fn `eq new_lemmas e

meta def simplify_goal (prove_fn : tactic unit) (extra_lemmas : list expr) : tactic unit :=
do (new_target, Heq) ← target >>= simplify prove_fn extra_lemmas,
   assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_app `eq.mpr [Heq, Ht] >>= exact

meta def simp : tactic unit :=
simplify_goal failed [] >> try triv >> try reflexivity

meta def simp_using (Hs : list expr) : tactic unit :=
simplify_goal failed Hs >> try triv

private meta def is_equation : expr → bool
| (expr.pi n bi d b) := is_equation b
| e                  := match (expr.is_eq e) with (some a) := tt | none := ff end

private meta def collect_eqs : list expr → tactic (list expr)
| []        := return []
| (H :: Hs) := do
  Eqs   ← collect_eqs Hs,
  Htype ← infer_type H >>= whnf,
  return $ if is_equation Htype then H :: Eqs else Eqs

/- Simplify target using all hypotheses in the local context. -/
meta def simp_using_hs : tactic unit :=
local_context >>= collect_eqs >>= simp_using

meta def simp_core_at (prove_fn : tactic unit) (extra_lemmas : list expr) (H : expr) : tactic unit :=
do when (expr.is_local_constant H = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   Htype ← infer_type H,
   (new_Htype, Heq) ← simplify prove_fn extra_lemmas Htype,
   assert (expr.local_pp_name H) new_Htype,
   mk_app `eq.mp [Heq, H] >>= exact,
   try $ clear H

meta def simp_at : expr → tactic unit :=
simp_core_at failed []

meta def simp_at_using (Hs : list expr) : expr → tactic unit :=
simp_core_at failed Hs

meta def simp_at_using_hs (H : expr) : tactic unit :=
do Hs ← local_context >>= collect_eqs,
   simp_core_at failed (filter (ne H) Hs) H

meta def mk_eq_simp_ext (simp_ext : expr → tactic (expr × expr)) : tactic unit :=
do (lhs, rhs)     ← target >>= match_eq,
   (new_rhs, Heq) ← simp_ext lhs,
   unify rhs new_rhs,
   exact Heq

/- Simp attribute support -/

meta def to_simp_lemmas : simp_lemmas → list name → tactic simp_lemmas
| S []      := return S
| S (n::ns) := do S' ← simp_lemmas_insert_constant S n, to_simp_lemmas S' ns

meta def mk_simp_attr (attr_name : name) : command :=
do t ← to_expr `(caching_user_attribute),
   a ← attr_name^.to_expr,
   v ← to_expr `({ caching_user_attribute .
                   name     := %%a,
                   descr    := "simplifier attribute",
                   cache    := simp_lemmas,
                   mk_cache := λ ns, do {tactic.to_simp_lemmas simp_lemmas.mk ns},
                   dependencies := [`reducible] }),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def get_user_simp_lemmas (attr_name : name) : tactic simp_lemmas :=
if attr_name = `default then mk_simp_lemmas
else do
  cnst   ← return (expr.const attr_name []),
  getter ← to_expr `(caching_user_attribute.get_cache %%cnst),
  tac    ← eval_expr (tactic simp_lemmas) getter,
  tac

meta def join_user_simp_lemmas_core : simp_lemmas → list name → tactic simp_lemmas
| S []             := return S
| S (attr_name::R) := do S' ← get_user_simp_lemmas attr_name, join_user_simp_lemmas_core (S^.join S') R

meta def join_user_simp_lemmas : list name → tactic simp_lemmas
| []         := mk_simp_lemmas
| attr_names := join_user_simp_lemmas_core simp_lemmas.mk attr_names

end tactic

export tactic (mk_simp_attr)
