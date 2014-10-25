-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import data.unit.decl data.unit.thms logic.decidable logic.inhabited
open decidable

namespace unit
  protected theorem subsingleton [instance] : subsingleton unit :=
  subsingleton.intro (λ a b, equal a b)

  protected definition is_inhabited [instance] : inhabited unit :=
  inhabited.mk ⋆

  protected definition has_decidable_eq [instance] : decidable_eq unit :=
  take (a b : unit), inl (equal a b)
end unit
