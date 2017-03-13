/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics init.meta.occurrences init.meta.quote
import init.data.option.instances

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

/- (Definitional) Simplify the given expression using *only* reflexivity equality lemmas from the given set of lemmas.
   The resulting expression is definitionally equal to the input. -/
meta constant simp_lemmas.dsimplify_core (max_steps : nat) (visit_instances : bool) : simp_lemmas → expr → tactic expr

meta constant is_valid_simp_lemma_cnst : transparency → name → tactic bool
meta constant is_valid_simp_lemma : transparency → expr → tactic bool

def default_max_steps := 10000000

meta def simp_lemmas.dsimplify : simp_lemmas → expr → tactic expr :=
simp_lemmas.dsimplify_core default_max_steps ff

meta constant simp_lemmas.pp : simp_lemmas → tactic format

namespace tactic
/- (get_eqn_lemmas_for deps d) returns the automatically generated equational lemmas for definition d.
   If deps is tt, then lemmas for automatically generated auxiliary declarations used to define d are also included. -/
meta constant get_eqn_lemmas_for : bool → name → tactic (list name)

meta constant dsimplify_core
  /- The user state type. -/
  {α : Type}
  /- Initial user data -/
  (a : α)
  (max_steps       : nat)
  /- If visit_instances = ff, then instance implicit arguments are not visited, but
     tactic will canonize them. -/
  (visit_instances : bool)
  /- (pre a e) is invoked before visiting the children of subterm 'e',
     if it succeeds the result (new_a, new_e, flag) where
       - 'new_a' is the new value for the user data
       - 'new_e' is a new expression that must be definitionally equal to 'e',
       - 'flag'  if tt 'new_e' children should be visited, and 'post' invoked. -/
  (pre             : α → expr → tactic (α × expr × bool))
  /- (post a e) is invoked after visiting the children of subterm 'e',
     The output is similar to (pre a e), but the 'flag' indicates whether
     the new expression should be revisited or not. -/
  (post            : α → expr → tactic (α × expr × bool))
  : expr → tactic (α × expr)

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
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← dunfold_occs_core reducible default_max_steps occs cs d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

meta def dunfold_at (cs : list name) (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← dunfold_core reducible default_max_steps cs d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

structure delta_config :=
(max_steps       := default_max_steps)
(visit_instances := tt)

private meta def is_delta_target (e : expr) (cs : list name) : bool :=
cs^.any (λ c,
  if e^.is_app_of c then tt   /- Exact match -/
  else let f := e^.get_app_fn in
       /- f is an auxiliary constant generated when compiling c -/
       f^.is_constant && f^.const_name^.is_internal && (f^.const_name^.get_prefix = c))

/- Delta reduce the given constant names -/
meta def delta_core (cfg : delta_config) (cs : list name) (e : expr) : tactic expr :=
let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
  guard (is_delta_target e cs),
  (expr.const f_name f_lvls) ← return e^.get_app_fn,
  env   ← get_env,
  decl  ← env^.get f_name,
  new_f ← decl^.instantiate_value_univ_params f_lvls,
  new_e ← head_beta (expr.mk_app new_f e^.get_app_args),
  return (u, new_e, tt)
in do (c, new_e) ← dsimplify_core () cfg^.max_steps cfg^.visit_instances (λ c e, failed) unfold e,
      return new_e

meta def delta (cs : list name) : tactic unit :=
target >>= delta_core {} cs >>= change

meta def delta_at (cs : list name) (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← delta_core {} cs d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

structure simp_config :=
(max_steps : nat           := default_max_steps)
(contextual : bool         := ff)
(lift_eq : bool            := tt)
(canonize_instances : bool := tt)
(canonize_proofs : bool    := ff)
(use_axioms : bool         := tt)
(zeta : bool               := tt)

meta constant simplify_core
  (c : simp_config)
  (s : simp_lemmas)
  (r : name) :
  expr → tactic (expr × expr)

meta constant ext_simplify_core
  /- The user state type. -/
  {α : Type}
  /- Initial user data -/
  (a : α)
  (c : simp_config)
  /- Congruence and simplification lemmas.
     Remark: the simplification lemmas at not applied automatically like in the simplify_core tactic.
     the caller must use them at pre/post. -/
  (s : simp_lemmas)
  /- Tactic for dischaging hypothesis in conditional rewriting rules.
     The argument 'α' is the current user state. -/
  (prove : α → tactic α)
  /- (pre a S r s p e) is invoked before visiting the children of subterm 'e',
     'r' is the simplification relation being used, 's' is the updated set of lemmas if 'contextual' is tt,
     'p' is the "parent" expression (if there is one).
     if it succeeds the result is (new_a, new_e, new_pr, flag) where
       - 'new_a' is the new value for the user data
       - 'new_e' is a new expression s.t. 'e r new_e'
       - 'new_pr' is a proof for 'e r new_e', If it is none, the proof is assumed to be by reflexivity
       - 'flag'  if tt 'new_e' children should be visited, and 'post' invoked. -/
  (pre : α → simp_lemmas → name → option expr → expr → tactic (α × expr × option expr × bool))
  /- (post a r s p e) is invoked after visiting the children of subterm 'e',
     The output is similar to (pre a r s p e), but the 'flag' indicates whether
     the new expression should be revisited or not. -/
  (post : α → simp_lemmas  → name → option expr → expr → tactic (α × expr × option expr × bool))
  /- simplification relation -/
  (r : name) :
  expr → tactic (α × expr × expr)

meta def simplify (S : simp_lemmas) (e : expr) (cfg : simp_config := {}) : tactic (expr × expr) :=
do e_type       ← infer_type e >>= whnf,
   simplify_core cfg S `eq e

meta def replace_target (new_target : expr) (pr : expr) : tactic unit :=
do assert `htarget new_target, swap,
   ht ← get_local `htarget,
   mk_eq_mpr pr ht >>= exact

meta def simplify_goal (S : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
do t ← target,
   (new_t, pr) ← simplify S t cfg,
   replace_target new_t pr

meta def simp (cfg : simp_config := {}) : tactic unit :=
do S ← simp_lemmas.mk_default,
simplify_goal S cfg >> try triv >> try (reflexivity reducible)

meta def simp_using (hs : list expr) (cfg : simp_config := {}) : tactic unit :=
do S ← simp_lemmas.mk_default,
   S ← S^.append hs,
simplify_goal S cfg >> try triv

meta def dsimp_core (s : simp_lemmas) : tactic unit :=
target >>= s^.dsimplify >>= change

meta def dsimp : tactic unit :=
simp_lemmas.mk_default >>= dsimp_core

meta def dsimp_at_core (s : simp_lemmas) (h : expr) : tactic unit :=
do num_reverted : ℕ ← revert h,
   expr.pi n bi d b ← target,
   h_simp ← s^.dsimplify d,
   change $ expr.pi n bi h_simp b,
   intron num_reverted

meta def dsimp_at (h : expr) : tactic unit :=
do s ← simp_lemmas.mk_default, dsimp_at_core s h

private meta def is_equation : expr → bool
| (expr.pi n bi d b) := is_equation b
| e                  := match (expr.is_eq e) with (some a) := tt | none := ff end

private meta def collect_simps : list expr → tactic (list expr)
| []        := return []
| (h :: hs) := do
  result ← collect_simps hs,
  htype  ← infer_type h >>= whnf,
  if is_equation htype
  then return (h :: result)
  else do
    pr ← is_prop htype,
    return $ if pr then (h :: result) else result

meta def collect_ctx_simps : tactic (list expr) :=
local_context >>= collect_simps

/-- Simplify target using all hypotheses in the local context. -/
meta def simp_using_hs (cfg : simp_config := {}) : tactic unit :=
do es ← collect_ctx_simps, simp_using es cfg

meta def simph (cfg : simp_config := {}) :=
simp_using_hs cfg

meta def intro1_aux : bool → list name → tactic expr
| ff _       := intro1
| tt (n::ns) := intro n
| _  _       := failed

meta def simp_intro_aux (cfg : simp_config) (updt : bool) : simp_lemmas → bool → list name → tactic simp_lemmas
| S tt     [] := try (simplify_goal S cfg) >> return S
| S use_ns ns := do
  t ← target,
  if t^.is_napp_of `not 1 then
    intro1_aux use_ns ns >> simp_intro_aux S use_ns ns^.tail
  else if t^.is_arrow then
    do {
      d ← return t^.binding_domain,
      (new_d, h_d_eq_new_d) ← simplify S d cfg,
      h_d ← intro1_aux use_ns ns,
      h_new_d ← mk_eq_mp h_d_eq_new_d h_d,
      assertv_core h_d^.local_pp_name new_d h_new_d,
      h_new   ← intro1,
      new_S ← if updt && is_equation new_d then S^.add h_new else return S,
      clear h_d,
      simp_intro_aux new_S use_ns ns
    }
    <|>
    -- failed to simplify... we just introduce and continue
    (intro1_aux use_ns ns >> simp_intro_aux S use_ns ns^.tail)
  else if t^.is_pi || t^.is_let then
    intro1_aux use_ns ns >> simp_intro_aux S use_ns ns^.tail
  else do
    new_t ← whnf t reducible,
    if new_t^.is_pi then change new_t >> simp_intro_aux S use_ns ns
    else
      try (simplify_goal S cfg) >>
      mcond (expr.is_pi <$> target)
        (simp_intro_aux S use_ns ns)
        (if use_ns ∧ ¬ns^.empty then failed else return S)

meta def simp_intros_using (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
step $ simp_intro_aux cfg ff s ff []

meta def simph_intros_using (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
step $
do s ← collect_ctx_simps >>= s^.append,
   simp_intro_aux cfg tt s ff []

meta def simp_intro_lst_using (ns : list name) (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
step $ simp_intro_aux cfg ff s tt ns

meta def simph_intro_lst_using (ns : list name) (s : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
step $
do s ← collect_ctx_simps >>= s^.append,
   simp_intro_aux cfg tt s tt ns

meta def simp_at (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S^.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   try $ clear h

meta def simp_at_using_hs (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do hs ← collect_ctx_simps,
   simp_at h (list.filter (≠ h) hs ++ extra_lemmas) cfg

meta def simph_at (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
simp_at_using_hs h extra_lemmas cfg

meta def mk_eq_simp_ext (simp_ext : expr → tactic (expr × expr)) : tactic unit :=
do (lhs, rhs)     ← target >>= match_eq,
   (new_rhs, heq) ← simp_ext lhs,
   unify rhs new_rhs,
   exact heq

/- Simp attribute support -/

meta def to_simp_lemmas : simp_lemmas → list name → tactic simp_lemmas
| S []      := return S
| S (n::ns) := do S' ← S^.add_simp n, to_simp_lemmas S' ns

meta def mk_simp_attr (attr_name : name) : command :=
do let t := ```(caching_user_attribute simp_lemmas),
   v ← to_expr ``({name     := %%(quote attr_name),
                   descr    := "simplifier attribute",
                   mk_cache := λ ns, do {tactic.to_simp_lemmas simp_lemmas.mk ns},
                   dependencies := [`reducibility] } : caching_user_attribute simp_lemmas),
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

/- Normalize numerical expression, returns a pair (n, pr) where n is the resultant numeral,
   and pr is a proof that the input argument is equal to n. -/
meta constant norm_num : expr → tactic (expr × expr)

meta def simplify_top_down {α} (a : α) (pre : α → expr → tactic (α × expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ a _ _ _ e, do (new_a, new_e, pr) ← pre a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, tt))
  (λ _ _ _ _ _, failed)
  `eq e

meta def simp_top_down (pre : expr → tactic (expr × expr)) (cfg : simp_config := {}) : tactic unit :=
do t                   ← target,
   (_, new_target, pr) ← simplify_top_down () (λ _ e, do (new_e, pr) ← pre e, return ((), new_e, pr)) t cfg,
   replace_target new_target pr

meta def simplify_bottom_up {α} (a : α) (post : α → expr → tactic (α × expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ _ _ _ _ _, failed)
  (λ a _ _ _ e, do (new_a, new_e, pr) ← post a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, tt))
  `eq e

meta def simp_bottom_up (post : expr → tactic (expr × expr)) (cfg : simp_config := {}) : tactic unit :=
do t                   ← target,
   (_, new_target, pr) ← simplify_bottom_up () (λ _ e, do (new_e, pr) ← post e, return ((), new_e, pr)) t cfg,
   replace_target new_target pr
end tactic

export tactic (mk_simp_attr)
