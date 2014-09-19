-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.core.decidable logic.core.inhabited
open decidable

inductive unit : Type :=
  star : unit
namespace unit
  notation `⋆`:max := star

  protected theorem equal (a b : unit) : a = b :=
  rec (rec rfl b) a

  theorem eq_star (a : unit) : a = star :=
  equal a star

  protected theorem is_inhabited [instance] : inhabited unit :=
  inhabited.mk ⋆

  protected theorem has_decidable_eq [instance] : decidable_eq unit :=
  take (a b : unit), inl (equal a b)
end unit
