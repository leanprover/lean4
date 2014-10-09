-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.decidable logic.inhabited
open decidable

inductive unit : Type :=
  star : unit
namespace unit
  notation `⋆`:max := star

  -- remove duplication?
  protected theorem equal (a b : unit) : a = b :=
  rec (rec rfl b) a

  protected theorem subsingleton [instance] : subsingleton unit :=
  subsingleton.intro (λ a b, equal a b)

  theorem eq_star (a : unit) : a = star :=
  equal a star

  protected definition is_inhabited [instance] : inhabited unit :=
  inhabited.mk ⋆

  protected definition has_decidable_eq [instance] : decidable_eq unit :=
  take (a b : unit), inl (equal a b)
end unit
