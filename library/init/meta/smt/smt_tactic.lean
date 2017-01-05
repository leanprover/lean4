/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.simp_tactic
import init.meta.smt.congruence_closure
import init.meta.smt.ematch

universe variables u

run_command mk_simp_attr `pre_smt
run_command mk_hinst_lemma_attr_set `ematch [] [`ematch_lhs]

/--
  Configuration for the smt tactic preprocessor. The preprocessor
  is applied whenever a new hypothesis is introduced.

  - simp_attr: is the attribute name for the simplification lemmas
    that are used during the preprocessing step.

  - max_steps: it is the maximum number of steps performed by the simplifier.

  - zeta: if tt, then zeta reduction (i.e., unfolding let-expressions)
    is used during preprocessing.
-/
structure smt_pre_config :=
(simp_attr : name)
(max_steps : nat)
(zeta      : bool)

def default_smt_pre_config : smt_pre_config :=
{ simp_attr := `pre_smt,
  max_steps := 1000000,
  zeta      := ff }

/--
Configuration for the smt_state object.

- em_attr: is the attribute name for the hinst_lemmas
  that are used for ematching -/
structure smt_config :=
(cc_cfg        : cc_config)
(em_cfg        : ematch_config)
(pre_cfg       : smt_pre_config)
(em_attr       : name)

def default_smt_config : smt_config :=
{cc_cfg        := default_cc_config,
 em_cfg        := default_ematch_config,
 pre_cfg       := default_smt_pre_config,
 em_attr       := `ematch}

meta def smt_config.set_classical (c : smt_config) (b : bool) : smt_config :=
{c with cc_cfg := { (c^.cc_cfg) with em := b}}

meta constant smt_goal                  : Type
meta def smt_state :=
list smt_goal
meta constant smt_state.mk              : smt_config → tactic smt_state
meta constant smt_state.to_format       : smt_state → tactic_state → format
/- The following returns tt if classical excluded middle was enabled at
   smt_state.mk -/
meta constant smt_state.classical       : smt_state → bool

meta def smt_tactic :=
state_t smt_state tactic

meta instance : monad smt_tactic :=
state_t.monad _ _

/- We don't use the default state_t lift operation because only
   tactics that do not change hypotheses can be automatically lifted to smt_tactic. -/
meta constant tactic_to_smt_tactic (α : Type) : tactic α → smt_tactic α

meta instance : monad.has_monad_lift tactic smt_tactic :=
⟨tactic_to_smt_tactic⟩

meta instance (α : Type) : has_coe (tactic α) (smt_tactic α) :=
⟨monad.monad_lift⟩

meta def smt_tactic_orelse {α : Type} (t₁ t₂ : smt_tactic α) : smt_tactic α :=
λ ss ts, tactic_result.cases_on (t₁ ss ts)
  tactic_result.success
  (λ e₁ ref₁ s', tactic_result.cases_on (t₂ ss ts)
     tactic_result.success
     (tactic_result.exception (α × smt_state)))

meta instance : alternative smt_tactic :=
{failure := λ α, @tactic.failed α,
 orelse  := @smt_tactic_orelse,
 pure    := @return _ _,
 seq     := @fapp _ _,
 map     := @fmap _ _}

namespace smt_tactic
open tactic (transparency)
/-- (intros_core fresh_names), if fresh_names is tt, then create fresh names for new hypotheses.
    Otherwise, it just uses the given names. -/
meta constant intros_core                     : bool → smt_tactic unit
meta constant close                           : smt_tactic unit
meta constant ematch_core                     : (expr → bool) → smt_tactic unit
meta constant add_ematch_lemma_core           : transparency → bool → expr → smt_tactic unit
meta constant add_ematch_lemma_from_decl_core : transparency → bool → name → smt_tactic unit
meta constant add_ematch_eqn_lemmas_for_core  : transparency → name → smt_tactic unit
meta constant to_cc_state                     : smt_tactic cc_state
meta constant to_em_state                     : smt_tactic ematch_state
meta constant preprocess                      : expr → smt_tactic (expr × expr)

meta def intros : smt_tactic unit :=
intros_core tt

meta def ematch : smt_tactic unit :=
ematch_core (λ _, tt)

meta def failed : smt_tactic unit :=
tactic.failed

meta def fail {α : Type} {β : Type u} [has_to_format β] (msg : β) : tactic α :=
tactic.fail msg

meta def try {α : Type} (t : smt_tactic α) : smt_tactic unit :=
λ ss ts, tactic_result.cases_on (t ss ts)
 (λ ⟨a, new_ss⟩, tactic_result.success ((), new_ss))
 (λ e ref s', tactic_result.success ((), ss) ts)

/- (repeat_at_most n t): repeat the given tactic at most n times or until t fails -/
meta def repeat_at_most : nat → smt_tactic unit → smt_tactic unit
| 0     t := return ()
| (n+1) t := (do t, repeat_at_most n t) <|> return ()

/- (repeat_exactly n t) : execute t n times -/
meta def repeat_exactly : nat → smt_tactic unit → smt_tactic unit
| 0     t := return ()
| (n+1) t := do t, repeat_exactly n t

meta def repeat : smt_tactic unit → smt_tactic unit :=
repeat_at_most 100000

open tactic

protected meta def read : smt_tactic (smt_state × tactic_state) :=
do s₁ ← state_t.read,
   s₂ ← tactic.read,
   return (s₁, s₂)

meta def trace_state : smt_tactic unit :=
do (s₁, s₂) ← smt_tactic.read,
   trace (smt_state.to_format s₁ s₂)

meta def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic unit :=
tactic.trace a

meta def classical : smt_tactic bool :=
do s ← state_t.read,
   return s^.classical

/- Low level primitives for managing set of goals -/
meta def get_goals : smt_tactic (list smt_goal × list expr) :=
do (g₁, _) ← smt_tactic.read,
   g₂ ← tactic.get_goals,
   return (g₁, g₂)

meta def set_goals : list smt_goal → list expr → smt_tactic unit :=
λ g₁ g₂ ss, tactic.set_goals g₂ >> return ((), g₁)

private meta def all_goals_core (tac : smt_tactic unit) : list smt_goal → list expr → list smt_goal → list expr → smt_tactic unit
| []        ts        acs act := set_goals acs (ts ++ act)
| (s :: ss) []        acs act := fail "ill-formed smt_state"
| (s :: ss) (t :: ts) acs act :=
  do set_goals [s] [t],
     tac,
     (new_ss, new_ts) ← get_goals,
     all_goals_core ss ts (acs ++ new_ss) (act ++ new_ts)

/- Apply the given tactic to all goals. -/
meta def all_goals (tac : smt_tactic unit) : smt_tactic unit :=
do (ss, ts) ← get_goals,
   all_goals_core tac ss ts [] []

/- LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
meta def seq (tac1 : smt_tactic unit) (tac2 : smt_tactic unit) : smt_tactic unit :=
do (s::ss, t::ts) ← get_goals | failed,
   set_goals [s] [t],
   tac1, all_goals tac2,
   (new_ss, new_ts) ← get_goals,
   set_goals (new_ss ++ ss) (new_ts ++ ts)

meta def swap : smt_tactic unit :=
do (ss, ts) ← get_goals,
   match ss, ts with
   | (s₁ :: s₂ :: ss), (t₁ :: t₂ :: ts) := set_goals (s₂ :: s₁ :: ss) (t₂ :: t₁ :: ts)
   | _,                _                := failed
   end

/- (assert h t), adds a new goal for t, and the hypothesis (h : t) in the current goal. -/
meta def assert (h : name) (t : expr) : smt_tactic unit :=
tactic.assert_core h t >> swap >> intros_core ff >> swap >> try close

/- (assertv h t v), adds the hypothesis (h : t) in the current goal if v has type t. -/
meta def assertv (h : name) (t : expr) (v : expr) : smt_tactic unit :=
tactic.assertv_core h t v >> intros_core ff >> return ()

/- (define h t), adds a new goal for t, and the hypothesis (h : t := ?M) in the current goal. -/
meta def define  (h : name) (t : expr) : smt_tactic unit :=
tactic.define_core h t >> swap >> intros_core ff >> swap >> try close

/- (definev h t v), adds the hypothesis (h : t := v) in the current goal if v has type t. -/
meta def definev (h : name) (t : expr) (v : expr) : smt_tactic unit :=
tactic.definev_core h t v >> intros_core ff >> return ()

/- Add (h : t := pr) to the current goal -/
meta def pose (h : name) (pr : expr) : smt_tactic unit :=
do t ← tactic.infer_type pr,
   definev h t pr

/- Add (h : t) to the current goal, given a proof (pr : t) -/
meta def note (n : name) (pr : expr) : smt_tactic unit :=
do t ← tactic.infer_type pr,
   assertv n t pr

meta def destruct (e : expr) : smt_tactic unit :=
smt_tactic.seq (tactic.destruct e) smt_tactic.intros

meta def by_cases (e : expr) : smt_tactic unit :=
do c ← classical,
   if c then
     destruct (expr.app (expr.const `classical.em []) e)
   else do
     dec_e ← (mk_app `decidable [e] <|> fail "by_cases smt_tactic failed, type is not a proposition"),
     inst  ← (mk_instance dec_e <|> fail "by_cases smt_tactic failed, type of given expression is not decidable"),
     em    ← mk_app `decidable.em [e, inst],
     destruct em

meta def by_contradiction : smt_tactic unit :=
do t ← target,
   c ← classical,
   if t^.is_false then skip
   else if c then do
      apply (expr.app (expr.const `classical.by_contradiction []) t),
      intros
   else do
     dec_t ← (mk_app `decidable [t] <|> fail "by_contradiction smt_tactic failed, target is not a proposition"),
     inst  ← (mk_instance dec_t <|> fail "by_contradiction smt_tactic failed, target is not decidable"),
     a     ← mk_mapp `decidable.by_contradiction [some t, some inst],
     apply a,
     intros

/- Return a proof for e, if 'e' is a known fact in the main goal. -/
meta def proof_for (e : expr) : smt_tactic expr :=
do cc ← to_cc_state, cc^.proof_for e

/- Return a refutation for e (i.e., a proof for (not e)), if 'e' has been refuted in the main goal. -/
meta def refutation_for (e : expr) : smt_tactic expr :=
do cc ← to_cc_state, cc^.refutation_for e

meta def get_facts : smt_tactic (list expr) :=
do cc ← to_cc_state,
   return $ cc^.eqc_of expr.mk_true

meta def get_refuted_facts : smt_tactic (list expr) :=
do cc ← to_cc_state,
   return $ cc^.eqc_of expr.mk_false

meta def add_ematch_lemma : expr → smt_tactic unit :=
add_ematch_lemma_core reducible ff

meta def add_ematch_lhs_lemma : expr → smt_tactic unit :=
add_ematch_lemma_core reducible tt

meta def add_ematch_lemma_from_decl : name → smt_tactic unit :=
add_ematch_lemma_from_decl_core reducible ff

meta def add_ematch_lhs_lemma_from_decl : name → smt_tactic unit :=
add_ematch_lemma_from_decl_core reducible ff

meta def add_ematch_eqn_lemmas_for : name → smt_tactic unit :=
add_ematch_eqn_lemmas_for_core reducible

meta def add_lemmas_from_facts_core : list expr → smt_tactic unit
| []      := return ()
| (f::fs) := do
  try (is_prop f >> guard (f^.is_pi && bnot (f^.is_arrow)) >> proof_for f >>= add_ematch_lemma_core reducible ff),
  add_lemmas_from_facts_core fs

meta def add_lemmas_from_facts : smt_tactic unit :=
get_facts >>= add_lemmas_from_facts_core

end smt_tactic

open smt_tactic

meta def using_smt_core (cfg : smt_config) (t : smt_tactic unit) : tactic unit :=
do ss ← smt_state.mk cfg,
   (t >> repeat close) ss,
   return ()

meta def using_smt : smt_tactic unit → tactic unit :=
using_smt_core default_smt_config
