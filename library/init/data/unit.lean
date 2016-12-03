/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic

lemma unit_eq (a b : unit) : a = b :=
unit.rec_on a (unit.rec_on b rfl)

lemma unit_eq_unit (a : unit) : a = () :=
unit_eq a ()

instance : subsingleton unit :=
subsingleton.intro unit_eq

instance : inhabited unit :=
⟨()⟩

instance : decidable_eq unit :=
λ a b, is_true (unit_eq a b)
