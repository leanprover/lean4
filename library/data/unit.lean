-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.classes.decidable logic.classes.inhabited
open decidable

inductive unit : Type :=
  star : unit
namespace unit
  notation `⋆`:max := star

  theorem equal [protected] (a b : unit) : a = b :=
  rec (rec rfl b) a

  theorem eq_star (a : unit) : a = star :=
  equal a star

  theorem is_inhabited [protected] [instance] : inhabited unit :=
  inhabited.mk ⋆

  theorem has_decidable_eq [protected] [instance] (a b : unit) : decidable (a = b) :=
  inl (equal a b)
end unit
