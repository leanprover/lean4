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

definition unit_subsingleton [instance] : subsingleton unit :=
subsingleton.intro unit_eq

definition unit_is_inhabited [instance] : inhabited unit :=
inhabited.mk ()
