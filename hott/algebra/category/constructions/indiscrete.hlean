/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Indiscrete category
-/

import .opposite

open functor is_trunc unit eq

namespace category

  variable (X : Type)

  definition indiscrete_precategory [constructor] : precategory X :=
  precategory.mk (λx y, unit)
                 (λx y z f g, star)
                 (λx, star)
                 (λx y z w f g h, idp)
                 (λx y f, by induction f; reflexivity)
                 (λx y f, by induction f; reflexivity)

  definition Indiscrete_precategory [constructor] : Precategory :=
  precategory.Mk (indiscrete_precategory X)

  definition indiscrete_op : (Indiscrete_precategory X)ᵒᵖ = Indiscrete_precategory X := idp

end category
