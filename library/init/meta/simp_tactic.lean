/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics init.meta.occurrences

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

   Result (new_e, pr) is the new expression 'new_e' and a proof (pr : e R new_e) -/
meta constant simp_lemmas.rewrite_core : transparency → simp_lemmas → tactic unit → name → expr → tactic (expr × expr)

meta def simp_lemmas.rewrite : simp_lemmas → tactic unit → name → expr → tactic (expr × expr) :=
simp_lemmas.rewrite_core reducible

/- (simp_lemmas.drewrite s e) tries to rewrite 'e' using only refl lemmas in 's' -/
meta constant simp_lemmas.drewrite_core : transparency → simp_lemmas → expr → tactic expr

meta def simp_lemmas.drewrite : simp_lemmas → expr → tactic expr :=
simp_lemmas.drewrite_core reducible

/- Simplify the given expression using [simp] and [congr] lemmas.
   The first argument is a tactic to be used to discharge proof obligations.
   The second argument is the name of the relation to simplify over.
   The third argument is a list of additional expressions to be considered as simp rules.
   The fourth argument is the expression to be simplified.
   The result is the simplified expression along with a proof that the new
   expression is equivalent to the old one.
   Fails if no simplifications can be performed. -/
meta constant simp_lemmas.simplify_core : simp_lemmas → tactic unit → name → expr → tactic (expr × expr)

/- (Definitional) Simplify the given expression using *only* reflexivity equality lemmas from the given set of lemmas.
   The resulting expression is definitionally equal to the input. -/
meta constant simp_lemmas.dsimplify_core (max_steps : nat) (visit_instances : bool) : simp_lemmas → expr → tactic expr

def default_max_steps := 10000000

meta def simp_lemmas.dsimplify : simp_lemmas → expr → tactic expr :=
simp_lemmas.dsimplify_core default_max_steps ff

namespace tactic
meta constant dsimplify_core
  /- The user state type. -/
  {A : Type}
  /- Initial user data -/
  (a : A)
  (max_steps       : nat)
  /- If visit_instances = ff, then instance implicit arguments are not visited, but
     tactic will canonize them. -/
  (visit_instances : bool)
  /- (pre a e) is invoked before visiting the children of subterm 'e',
     if it succeeds the result (new_a, new_e, flag) where
       - 'new_a' is the new value for the user data
       - 'new_e' is a new expression that must be definitionally equal to 'e',
       - 'flag'  if tt 'new_e' children should be visited, and 'post' invoked. -/
  (pre             : A → expr → tactic (A × expr × bool))
  /- (post a e) is invoked after visiting the children of subterm 'e',
     The output is similar to (pre a e), but the 'flag' indicates whether
     the new expression should be revisited or not. -/
  (post            : A → expr → tactic (A × expr × bool))
  : expr → tactic (A × expr)

meta def dsimplify
  (pre             : expr → tactic (expr × bool))
  (post            : expr → tactic (expr × bool))
  : expr → tactic expr :=
λ e, do (a, new_e) ← dsimplify_core () default_max_steps ff
                       (λ u e, do r ← pre e, return (u, r))
                       (λ u e, do r ← post e, return (u, r)) e,
        return new_e

meta constant dunfold_expr_core : transparency → expr → tactic expr

meta def dunfold_expr : expr → tactic expr :=
dunfold_expr_core reducible

meta constant unfold_projection_core : transparency → expr → tactic expr

meta def unfold_projection : expr → tactic expr :=
unfold_projection_core reducible

meta def dunfold_occs_core (m : transparency) (max_steps : nat) (occs : occurrences) (cs : list name) (e : expr) : tactic expr :=
let unfold (c : nat) (e : expr) : tactic (nat × expr × bool) := do
  guard (cs^.any e^.is_app_of),
  new_e ← dunfold_expr_core m e,
  if occs^.contains c
  then return (c+1, new_e, tt)
  else return (c+1, e, tt)
in do (c, new_e) ← dsimplify_core 1 max_steps tt unfold (λ c e, failed) e,
      return new_e

meta def dunfold_core (m : transparency) (max_steps : nat) (cs : list name) (e : expr) : tactic expr :=
let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
  guard (cs^.any e^.is_app_of),
  new_e ← dunfold_expr_core m e,
  return (u, new_e, tt)
in do (c, new_e) ← dsimplify_core () max_steps tt (λ c e, failed) unfold e,
      return new_e

meta def dunfold : list name → tactic unit :=
λ cs, target >>= dunfold_core reducible default_max_steps cs >>= change

meta def dunfold_occs_of (occs : list nat) (c : name) : tactic unit :=
target >>= dunfold_occs_core reducible default_max_steps (occurrences.pos occs) [c] >>= change

meta def dunfold_core_at (occs : occurrences) (cs : list name) (h : expr) : tactic unit :=
do num_reverted : ℕ ← revert h,
   (expr.pi n bi d b : expr) ← target | failed,
   new_d : expr ← dunfold_occs_core reducible default_max_steps occs cs d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

meta def dunfold_at (cs : list name) (h : expr) : tactic unit :=
do num_reverted : ℕ ← revert h,
   (expr.pi n bi d b : expr) ← target | failed,
   new_d : expr ← dunfold_core reducible default_max_steps cs d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

structure simplify_config :=
(max_steps : nat)
(contextual : bool)
(lift_eq : bool)
(canonize_instances : bool)
(canonize_proofs : bool)
(use_axioms : bool)

def default_simplify_config : simplify_config :=
{ max_steps  := default_max_steps,
  contextual := ff,
  lift_eq    := tt,
  canonize_instances := tt,
  canonize_proofs    := ff,
  use_axioms := tt }

meta constant simplify_core
  (c : simplify_config)
  (s : simp_lemmas)
  (r : name) :
  expr → tactic (expr × expr)

meta constant ext_simplify_core
  /- The user state type. -/
  {A : Type}
  /- Initial user data -/
  (a : A)
  (c : simplify_config)
  /- Congruence and simplification lemmas.
     Remark: the simplification lemmas at not applied automatically like in the simplify_core tactic.
     the caller must use them at pre/post. -/
  (s : simp_lemmas)
  /- Tactic for dischaging hypothesis in conditional rewriting rules.
     The argument 'A' is the current user state. -/
  (prove : A → tactic A)
  /- (pre a r s p e) is invoked before visiting the children of subterm 'e',
     'r' is the simplification relation being used, 's' is the updated set of lemmas if 'contextual' is tt,
     'p' is the "parent" expression (if there is one).
     if it succeeds the result is (new_a, new_e, new_pr, flag) where
       - 'new_a' is the new value for the user data
       - 'new_e' is a new expression s.t. 'e r new_e'
       - 'new_pr' is a proof for 'e r new_e', If it is none, the proof is assumed to be by reflexivity
       - 'flag'  if tt 'new_e' children should be visited, and 'post' invoked. -/
  (pre : A → name → simp_lemmas → option expr → expr → tactic (A × expr × option expr × bool))
  /- (post a r s p e) is invoked after visiting the children of subterm 'e',
     The output is similar to (pre a r s p e), but the 'flag' indicates whether
     the new expression should be revisited or not. -/
  (post : A → name → simp_lemmas → option expr → expr → tactic (A × expr × option expr × bool))
  /- simplification relation -/
  (r : name) :
  expr → tactic (A × expr × expr)

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

meta def dsimp : tactic unit :=
do S ← simp_lemmas.mk_default,
   target >>= S^.dsimplify >>= change

meta def dsimp_at (H : expr) : tactic unit :=
do num_reverted : ℕ ← revert H,
   (expr.pi n bi d b : expr) ← target | failed,
   S      ← simp_lemmas.mk_default,
   H_simp ← S^.dsimplify d,
   change $ expr.pi n bi H_simp b,
   intron num_reverted

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
