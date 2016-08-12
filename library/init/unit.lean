/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic

theorem unit_eq (a b : unit) : a = b :=
unit.rec_on a (unit.rec_on b rfl)

theorem unit_eq_unit (a : unit) : a = () :=
unit_eq a ()

attribute [instance]
definition unit_subsingleton : subsingleton unit :=
subsingleton.intro unit_eq

attribute [instance]
definition unit_is_inhabited : inhabited unit :=
inhabited.mk ()
