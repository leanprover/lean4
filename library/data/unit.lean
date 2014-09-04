-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.classes.decidable logic.classes.inhabited

open decidable

inductive unit : Type :=
star : unit

namespace unit

notation `⋆`:max := star

theorem at_most_one (a b : unit) : a = b :=
rec (rec rfl b) a

theorem eq_star (a : unit) : a = star :=
at_most_one a star

theorem unit_inhabited [instance] : inhabited unit :=
inhabited.mk ⋆

theorem decidable_eq [instance] (a b : unit) : decidable (a = b) :=
inl (at_most_one a b)

end unit
