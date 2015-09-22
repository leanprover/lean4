/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Initial category
-/

import .indiscrete

open functor is_trunc eq

namespace category

  definition initial_precategory [constructor] : precategory empty :=
  indiscrete_precategory empty

  definition Initial_precategory [constructor] : Precategory :=
  precategory.Mk initial_precategory

  notation 0 := Initial_precategory
  definition zero_op : 0ᵒᵖ = 0 := idp

  definition initial_functor [constructor] (C : Precategory) : 0 ⇒ C :=
  functor.mk (λx, empty.elim x)
             (λx y f, empty.elim x)
             (λx, empty.elim x)
             (λx y z g f, empty.elim x)

  definition is_contr_zero_functor [instance] (C : Precategory) : is_contr (0 ⇒ C) :=
  is_contr.mk (initial_functor C)
              begin
                intro F, fapply functor_eq,
                { intro x, exact empty.elim x},
                { intro x y f, exact empty.elim x}
              end

  definition initial_functor_op (C : Precategory)
    : (initial_functor C)ᵒᵖ = initial_functor Cᵒᵖ :=
  by apply @is_hprop.elim (0 ⇒ Cᵒᵖ)

  definition initial_functor_comp {C D : Precategory} (F : C ⇒ D)
    : F ∘f initial_functor C = initial_functor D :=
  by apply @is_hprop.elim (0 ⇒ D)

end category
