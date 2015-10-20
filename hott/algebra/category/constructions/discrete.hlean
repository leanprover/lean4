/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Discrete category
-/

import ..groupoid types.bool ..functor.functor

open eq is_trunc iso bool functor

namespace category

  definition precategory_of_1_type [constructor] (A : Type) [H : is_trunc 1 A] : precategory A :=
  @precategory.mk _ _ (@is_trunc_eq _ _ H)
    (λ (a b c : A) (p : b = c) (q : a = b), q ⬝ p)
    (λ (a : A), refl a)
    (λ (a b c d : A) (p : c = d) (q : b = c) (r : a = b), con.assoc r q p)
    (λ (a b : A) (p : a = b), con_idp p)
    (λ (a b : A) (p : a = b), idp_con p)

  definition groupoid_of_1_type [constructor] (A : Type) [H : is_trunc 1 A] : groupoid A :=
  groupoid.mk !precategory_of_1_type
              (λ (a b : A) (p : a = b), is_iso.mk !con.right_inv !con.left_inv)

  definition Precategory_of_1_type [constructor] (A : Type) [H : is_trunc 1 A] : Precategory :=
  precategory.Mk (precategory_of_1_type A)

  definition Groupoid_of_1_type [constructor] (A : Type) [H : is_trunc 1 A] : Groupoid :=
  groupoid.Mk _ (groupoid_of_1_type A)

  definition discrete_precategory [constructor] (A : Type) [H : is_hset A] : precategory A :=
  precategory_of_1_type A

  definition discrete_groupoid [constructor] (A : Type) [H : is_hset A] : groupoid A :=
  groupoid_of_1_type A

  definition Discrete_precategory [constructor] (A : Type) [H : is_hset A] : Precategory :=
  precategory.Mk (discrete_precategory A)

  definition Discrete_groupoid [constructor] (A : Type) [H : is_hset A] : Groupoid :=
  groupoid.Mk _ (discrete_groupoid A)

  definition c2 [constructor] : Precategory := Discrete_precategory bool
  definition c1 [constructor] : Precategory := Discrete_precategory unit

  definition c2_functor [constructor] (C : Precategory) (x y : C) : c2 ⇒ C :=
  functor.mk (bool.rec x y)
             (bool.rec (bool.rec (λf, id) (by contradiction))
                       (bool.rec (by contradiction) (λf, id)))
             abstract (bool.rec idp idp) end
             abstract begin intro b₁ b₂ b₃ g f, induction b₁: induction b₂: induction b₃:
                            esimp at *: try contradiction: exact !id_id⁻¹ end end

end category
