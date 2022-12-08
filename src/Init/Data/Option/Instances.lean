/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic

universe u v

theorem Option.eq_of_eq_some {α : Type u} : ∀ {x y : Option α}, (∀z, x = some z ↔ y = some z) → x = y
  | none,   none,   _ => rfl
  | none,   some z, h => Option.noConfusion ((h z).2 rfl)
  | some z, none,   h => Option.noConfusion ((h z).1 rfl)
  | some _, some w, h => Option.noConfusion ((h w).2 rfl) (congrArg some)

theorem Option.eq_none_of_isNone {α : Type u} : ∀ {o : Option α}, o.isNone → o = none
  | none, _ => rfl
