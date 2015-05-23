/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import logic.eq

namespace unit
  notation `⋆` := star

  protected theorem equal (a b : unit) : a = b :=
  unit.rec_on a (unit.rec_on b rfl)

  theorem eq_star (a : unit) : a = star :=
  unit.equal a star

  protected theorem subsingleton [instance] : subsingleton unit :=
  subsingleton.intro (λ a b, unit.equal a b)

  protected definition is_inhabited [instance] : inhabited unit :=
  inhabited.mk unit.star

  protected definition has_decidable_eq [instance] : decidable_eq unit :=
  take (a b : unit), decidable.inl (unit.equal a b)
end unit
