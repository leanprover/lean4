/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic
universes u v

namespace tactic
meta constant ref (α : Type u) : Type u
/-- Create a new reference `r` with initial value `a`, execute `t r`, and then delete `r`. -/
meta constant using_new_ref {α : Type u} {β : Type v} (a : α) (t : ref α → tactic β) : tactic β
/-- Read the value stored in the given reference. -/
meta constant read_ref {α : Type u} : ref α → tactic α
/-- Update the value stored in the given reference. -/
meta constant write_ref {α : Type u} : ref α → α → tactic unit
end tactic
