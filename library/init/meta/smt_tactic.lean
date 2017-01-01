/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.congruence_tactics init.category.transformers

universe variables u

structure smt_config :=
(cc_cfg : cc_config)
(em_cfg : ematch_config)

def default_smt_config : smt_config :=
{cc_cfg := default_cc_config,
 em_cfg := default_ematch_config}

meta constant smt_state                 : Type
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

namespace smt_tactic
open tactic

protected meta def read : smt_tactic (smt_state × tactic_state) :=
do s₁ ← state_t.read,
   s₂ ← tactic.read,
   return (s₁, s₂)

meta def trace_state : smt_tactic unit :=
do (s₁, s₂) ← smt_tactic.read,
   trace (smt_state.to_format s₁ s₂)

end smt_tactic

meta def using_smt_core (cfg : smt_config) (t : smt_tactic unit) : tactic unit :=
do ss ← smt_state.mk cfg,
   t ss,
   return ()

meta def using_smt : smt_tactic unit → tactic unit :=
using_smt_core default_smt_config
