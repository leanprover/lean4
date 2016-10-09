/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics

open tactic

meta constant simp_lemmas : Type
meta constant simp_lemmas.mk : simp_lemmas
meta constant simp_lemmas.join : simp_lemmas → simp_lemmas → simp_lemmas
meta constant simp_lemmas.erase : simp_lemmas → list name → simp_lemmas
meta constant simp_lemmas.mk_default_core : transparency → tactic simp_lemmas
meta constant simp_lemmas.add_core : transparency → simp_lemmas → expr → tactic simp_lemmas
meta constant simp_lemmas.add_simp_core : transparency → simp_lemmas → name → tactic simp_lemmas
meta constant simp_lemmas.add_congr_core : transparency → simp_lemmas → name → tactic simp_lemmas

meta def simp_lemmas.mk_default : tactic simp_lemmas :=
simp_lemmas.mk_default_core reducible

meta def simp_lemmas.add : simp_lemmas → expr → tactic simp_lemmas :=
simp_lemmas.add_core reducible

meta def simp_lemmas.add_simp : simp_lemmas → name → tactic simp_lemmas :=
simp_lemmas.add_simp_core reducible

meta def simp_lemmas.add_congr : simp_lemmas → name → tactic simp_lemmas :=
simp_lemmas.add_congr_core reducible

meta def simp_lemmas.append : simp_lemmas → list expr → tactic simp_lemmas
| sls []      := return sls
| sls (l::ls) := do
  new_sls ← simp_lemmas.add sls l,
  simp_lemmas.append new_sls ls

/- (simp_lemmas.rewrite_core m s prove R e) apply a simplification lemma from 's'

   - 'prove' is used to discharge proof obligations.
   - 'R'     is the equivalence relation being used (e.g., 'eq', 'iff')
   - 'e'     is the expression to be "simplified"

   Result (new_e, pr) is the new expression 'new_e' and a proof (pr : e R new_e)
-/
meta constant simp_lemmas.rewrite_core : transparency → simp_lemmas → tactic unit → name → expr → tactic (expr × expr)

meta def simp_lemmas.rewrite : simp_lemmas → tactic unit → name → expr → tactic (expr × expr) :=
simp_lemmas.rewrite_core reducible

/- Simplify the given expression using [simp] and [congr] lemmas.
   The first argument is a tactic to be used to discharge proof obligations.
   The second argument is the name of the relation to simplify over.
   The third argument is a list of additional expressions to be considered as simp rules.
   The fourth argument is the expression to be simplified.
   The result is the simplified expression along with a proof that the new
   expression is equivalent to the old one.
   Fails if no simplifications can be performed. -/
meta constant simp_lemmas.simplify_core : simp_lemmas → tactic unit → name → expr → tactic (expr × expr)

namespace tactic

meta def simplify (prove_fn : tactic unit) (extra_lemmas : list expr) (e : expr) : tactic (expr × expr) :=
do lemmas       ← simp_lemmas.mk_default,
   new_lemmas   ← lemmas^.append extra_lemmas,
   e_type       ← infer_type e >>= whnf,
   new_lemmas^.simplify_core prove_fn `eq e

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
   simp_core_at failed (list.filter (ne H) Hs) H

meta def mk_eq_simp_ext (simp_ext : expr → tactic (expr × expr)) : tactic unit :=
do (lhs, rhs)     ← target >>= match_eq,
   (new_rhs, Heq) ← simp_ext lhs,
   unify rhs new_rhs,
   exact Heq

/- Simp attribute support -/

meta def to_simp_lemmas : simp_lemmas → list name → tactic simp_lemmas
| S []      := return S
| S (n::ns) := do S' ← S^.add_simp n, to_simp_lemmas S' ns

meta def mk_simp_attr (attr_name : name) : command :=
do t ← to_expr `(caching_user_attribute simp_lemmas),
   a ← attr_name^.to_expr,
   v ← to_expr `(({ name     := %%a,
                    descr    := "simplifier attribute",
                    mk_cache := λ ns, do {tactic.to_simp_lemmas simp_lemmas.mk ns},
                    dependencies := [`reducibility] } : caching_user_attribute simp_lemmas)),
   add_decl (declaration.defn attr_name [] t v reducibility_hints.abbrev ff),
   attribute.register attr_name

meta def get_user_simp_lemmas (attr_name : name) : tactic simp_lemmas :=
if attr_name = `default then simp_lemmas.mk_default
else do
  cnst   ← return (expr.const attr_name []),
  attr   ← eval_expr (caching_user_attribute simp_lemmas) cnst,
  caching_user_attribute.get_cache attr

meta def join_user_simp_lemmas_core : simp_lemmas → list name → tactic simp_lemmas
| S []             := return S
| S (attr_name::R) := do S' ← get_user_simp_lemmas attr_name, join_user_simp_lemmas_core (S^.join S') R

meta def join_user_simp_lemmas : list name → tactic simp_lemmas
| []         := simp_lemmas.mk_default
| attr_names := join_user_simp_lemmas_core simp_lemmas.mk attr_names

end tactic

export tactic (mk_simp_attr)
