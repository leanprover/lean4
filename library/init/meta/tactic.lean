/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.function init.data.option.basic init.util
import init.control.combinators init.control.monad init.control.alternative init.control.monad_fail
import init.data.nat.div init.meta.format
import init.data.repr init.data.string.basic init.meta.interaction_monad

meta constant tactic_state : Type

universes u v

namespace tactic_state
end tactic_state


@[reducible] meta def tactic := interaction_monad tactic_state
@[reducible] meta def tactic_result := interaction_monad.result tactic_state

namespace tactic
  export interaction_monad (hiding failed fail)
  meta def failed {α : Type} : tactic α := interaction_monad.failed
  meta def fail {α : Type u} {β : Type v} [has_to_format β] (msg : β) : tactic α :=
  interaction_monad.fail msg
end tactic

namespace tactic_result
  export interaction_monad.result
end tactic_result

open tactic
open tactic_result

infixl ` >>=[tactic] `:2 := interaction_monad_bind
infixl ` >>[tactic] `:2  := interaction_monad_seq

meta instance : alternative tactic :=
{ failure := @interaction_monad.failed _,
  orelse  := @interaction_monad_orelse _,
  ..interaction_monad.monad }

namespace tactic
variables {α : Type u}

@[inline] meta def write (s' : tactic_state) : tactic unit :=
λ s, success () s'

@[inline] meta def read : tactic tactic_state :=
λ s, success s s

end tactic

meta class has_to_tactic_format (α : Type u) :=
(to_tactic_format : α → tactic format)

meta def tactic.pp {α : Type u} [has_to_tactic_format α] : α → tactic format :=
has_to_tactic_format.to_tactic_format

open tactic format

@[priority 10] meta instance has_to_format_to_has_to_tactic_format (α : Type) [has_to_format α] : has_to_tactic_format α :=
⟨(λ x, pure x) ∘ to_fmt⟩

namespace tactic
open tactic_state

meta def trace {α : Type u} [has_to_tactic_format α] (a : α) : tactic unit :=
do fmt ← pp a,
   pure $ _root_.trace_fmt fmt (λ u, ())

end tactic

notation [parsing_only] `command`:max := tactic unit

meta def monad_from_pure_bind {m : Type u → Type v}
  (pure : Π {α : Type u}, α → m α)
  (bind : Π {α β : Type u}, m α → (α → m β) → m β) : monad m :=
{pure := @pure, bind := @bind}
