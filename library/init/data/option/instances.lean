/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import .basic
import init.meta.tactic


universes u v

@[inline] def option_bind {α : Type u} {β : Type v} : option α → (α → option β) → option β
| none     b := none
| (some a) b := b a

instance : monad option :=
{pure := @some, bind := @option_bind,
 id_map := λ α x, option.rec rfl (λ x, rfl) x,
 pure_bind := λ α β x f, rfl,
 bind_assoc := λ α β γ x f g, option.rec rfl (λ x, rfl) x}

def option_orelse {α : Type u} : option α → option α → option α
| (some a) o         := some a
| none     (some a)  := some a
| none     none      := none

instance : alternative option :=
{ option.monad with
  failure := @none,
  orelse  := @option_orelse }
