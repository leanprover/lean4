/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.base_tactic init.meta.environment

meta_constant tactic_state : Type₁

namespace tactic_state
meta_constant env : tactic_state → environment
end tactic_state

open tactic

meta_definition tactic [reducible] (A : Type) := base_tactic tactic_state A

meta_definition get_env : tactic environment :=
do s ← read,
   return (tactic_state.env s)
