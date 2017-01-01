/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.congruence_tactics init.category.transformers

structure smt_config :=
(cc_cfg : cc_config)
(em_cfg : ematch_config)

def default_smt_config : smt_config :=
{cc_cfg := default_cc_config,
 em_cfg := default_ematch_config}

meta constant smt_state                 : Type
meta constant smt_state.mk              : smt_config → tactic smt_state
meta constant smt_state.to_cc_state     : smt_state → cc_state
meta constant smt_state.to_ematch_state : smt_state → ematch_state
meta constant smt_state.to_format       : smt_state → tactic_state → format

meta def stactic :=
state_t smt_state tactic

/- We don't use the default state_t lift operation because only
   tactics that do not change hypotheses can be safely lifted to a
   stactic. -/
meta def tactic_to_stactic (α : Type) : tactic α → stactic α :=
λ t s₁ s₂, match t s₂ with
| tactic_result.success a new_s₂   := tactic_result.success (a, s₁) new_s₂
| tactic_result.exception .α f o s := tactic_result.exception (α × smt_state) f o s
end

meta instance : monad stactic := state_t.monad _ _

meta instance : monad.has_monad_lift tactic stactic :=
monad.monad_transformer_lift (state_t smt_state) tactic

namespace stactic
open tactic

meta def read : stactic (smt_state × tactic_state) :=
do s₁ ← state_t.read,
   s₂ ← tactic.read,
   return (s₁, s₂)

meta def trace_state : stactic unit :=
do (s₁, s₂) ← read,
   trace (smt_state.to_format s₁ s₂)

end stactic
