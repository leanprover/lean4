/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.option.basic

universes u v

lemma option.eqOfEqSome {α : Type u} : Π {x y : option α}, (∀z, x = some z ↔ y = some z) → x = y
| none     none     h := rfl
| none     (some z) h := option.noConfusion ((h z).2 rfl)
| (some z) none     h := option.noConfusion ((h z).1 rfl)
| (some z) (some w) h := option.noConfusion ((h w).2 rfl) (congrArg some)

lemma option.eqNoneOfIsNone {α : Type u} : Π {o : option α}, o.isNone → o = none
| none h := rfl
