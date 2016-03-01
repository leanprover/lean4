/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the unit type
-/

open equiv option eq

namespace unit

  protected definition eta : Π(u : unit), ⋆ = u
  | eta ⋆ := idp

  definition unit_equiv_option_empty [constructor] : unit ≃ option empty :=
  begin
    fapply equiv.MK,
    { intro u, exact none},
    { intro e, exact star},
    { intro e, cases e, reflexivity, contradiction},
    { intro u, cases u, reflexivity},
  end

  -- equivalences involving unit and other type constructors are in the file
  -- of the other constructor

end unit

open unit is_trunc
