/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Terminal category
-/

import .indiscrete

open functor is_trunc unit eq

namespace category

  definition terminal_precategory [constructor] : precategory unit :=
  indiscrete_precategory unit

  definition Terminal_precategory [constructor] : Precategory :=
  precategory.Mk terminal_precategory

  notation 1 := Terminal_precategory
  definition one_op : 1ᵒᵖ = 1 := idp

  definition terminal_functor [constructor] (C : Precategory) : C ⇒ 1 :=
  functor.mk (λx, star)
             (λx y f, star)
             (λx, idp)
             (λx y z g f, idp)

  definition is_contr_functor_one [instance] (C : Precategory) : is_contr (C ⇒ 1) :=
  is_contr.mk (terminal_functor C)
              begin
                intro F, fapply functor_eq,
                { intro x, apply @is_prop.elim unit},
                { intro x y f, apply @is_prop.elim unit}
              end

  definition terminal_functor_op (C : Precategory)
    : (terminal_functor C)ᵒᵖᶠ = terminal_functor Cᵒᵖ := idp

  definition terminal_functor_comp {C D : Precategory} (F : C ⇒ D)
    : (terminal_functor D) ∘f F = terminal_functor C := idp

  definition point [constructor] (C : Precategory) (c : C) : 1 ⇒ C :=
  functor.mk (λx, c)
             (λx y f, id)
             (λx, idp)
             (λx y z g f, !id_id⁻¹)

  -- we need id_id in the declaration of precategory to make this to hold definitionally
  definition point_op (C : Precategory) (c : C) : (point C c)ᵒᵖᶠ = point Cᵒᵖ c := idp

  definition point_comp {C D : Precategory} (F : C ⇒ D) (c : C)
    : F ∘f point C c = point D (F c) := idp

end category
