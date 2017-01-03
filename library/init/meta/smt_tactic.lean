/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.congruence_tactics init.category.transformers
import init.meta.simp_tactic

universe variables u

run_command mk_simp_attr `pre_smt

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
-/
structure smt_config :=
(cc_cfg        : cc_config)
(em_cfg        : ematch_config)
(pre_cfg       : smt_pre_config)

def default_smt_config : smt_config :=
{cc_cfg        := default_cc_config,
 em_cfg        := default_ematch_config,
 pre_cfg       := default_smt_pre_config}

meta constant smt_goal                  : Type
meta def smt_state :=
list smt_goal
meta constant smt_state.mk              : smt_config → tactic smt_state
meta constant smt_state.to_format       : smt_state → tactic_state → format

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
meta constant intros    : smt_tactic unit
meta constant close     : smt_tactic unit

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

meta def destruct (e : expr) : smt_tactic unit :=
smt_tactic.seq (tactic.destruct e) smt_tactic.intros

end smt_tactic

open smt_tactic

meta def using_smt_core (cfg : smt_config) (t : smt_tactic unit) : tactic unit :=
do ss ← smt_state.mk cfg,
   (t >> repeat close) ss,
   return ()

meta def using_smt : smt_tactic unit → tactic unit :=
using_smt_core default_smt_config
