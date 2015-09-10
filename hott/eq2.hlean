/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about 2-dimensional paths
-/

import .cubical.square
open function

namespace eq
  variables {A B C : Type} {f : A → B} {a a' a₁ a₂ a₃ a₄ : A} {b b' : B}

  theorem ap_is_constant_eq (p : Πx, f x = b) (q : a = a') :
      ap_is_constant p q =
      eq_con_inv_of_con_eq ((eq_of_square (square_of_pathover (apdo p q)))⁻¹ ⬝
      whisker_left (p a) (ap_constant q b)) :=
  begin
    induction q, esimp, generalize (p a), intro p, cases p, apply idpath idp
  end

  definition ap_inv2 {p q : a = a'} (r : p = q)
    : square (ap (ap f) (inverse2 r))
             (inverse2 (ap (ap f) r))
             (ap_inv f p)
             (ap_inv f q) :=
  by induction r;exact hrfl

  definition ap_con2 {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : square (ap (ap f) (r₁ ◾ r₂))
             (ap (ap f) r₁ ◾ ap (ap f) r₂)
             (ap_con f p₁ p₂)
             (ap_con f q₁ q₂) :=
  by induction r₂;induction r₁;exact hrfl

  theorem ap_con_right_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.right_inv p))
           (con.right_inv (ap f p))
           (ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p))
           idp :=
  by cases p;apply hrefl

  theorem ap_con_left_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.left_inv p))
           (con.left_inv (ap f p))
           (ap_con f p⁻¹ p ⬝ whisker_right (ap_inv f p) _)
           idp :=
  by cases p;apply vrefl

  theorem ap_ap_is_constant {A B C : Type} (g : B → C) {f : A → B} {b : B}
    (p : Πx, f x = b) {x y : A} (q : x = y) :
    square (ap (ap g) (ap_is_constant p q))
           (ap_is_constant (λa, ap g (p a)) q)
           (ap_compose g f q)⁻¹
           (!ap_con ⬝ whisker_left _ !ap_inv) :=
  begin
    induction q, esimp, generalize (p x), intro p, cases p, apply ids
--    induction q, rewrite [↑ap_compose,ap_inv], apply hinverse, apply ap_con_right_inv_sq,
  end

  theorem ap_ap_compose {A B C D : Type} (h : C → D) (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose (h ∘ g) f p)
           (ap (ap h) (ap_compose g f p))
           (ap_compose h (g ∘ f) p)
           (ap_compose h g (ap f p)) :=
  by induction p;exact ids

  theorem ap_compose_inv {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose g f p⁻¹)
           (inverse2 (ap_compose g f p) ⬝ (ap_inv g (ap f p))⁻¹)
           (ap_inv (g ∘ f) p)
           (ap (ap g) (ap_inv f p)) :=
  by induction p;exact ids

  theorem ap_compose_con (g : B → C) (f : A → B) (p : a₁ = a₂) (q : a₂ = a₃) :
    square (ap_compose g f (p ⬝ q))
           (ap_compose g f p ◾ ap_compose g f q ⬝ (ap_con g (ap f p) (ap f q))⁻¹)
           (ap_con (g ∘ f) p q)
           (ap (ap g) (ap_con f p q)) :=
  by induction q;induction p;exact ids

  theorem ap_compose_natural {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} {p q : x = y} (r : p = q) :
    square (ap (ap (g ∘ f)) r)
           (ap (ap g ∘ ap f) r)
           (ap_compose g f p)
           (ap_compose g f q) :=
  natural_square (ap_compose g f) r

  theorem ap_eq_of_con_inv_eq_idp (f : A → B) {p q : a₁ = a₂} (r : p ⬝ q⁻¹ = idp)
  : ap02 f (eq_of_con_inv_eq_idp r) =
           eq_of_con_inv_eq_idp (whisker_left _ !ap_inv⁻¹ ⬝ !ap_con⁻¹ ⬝ ap02 f r)
            :=
  by induction q;esimp at *;cases r;reflexivity

  theorem eq_of_con_inv_eq_idp_con2 {p p' q q' : a₁ = a₂} (r : p = p') (s : q = q')
    (t : p' ⬝ q'⁻¹ = idp)
  : eq_of_con_inv_eq_idp (r ◾ inverse2 s ⬝ t) = r ⬝ eq_of_con_inv_eq_idp t ⬝ s⁻¹ :=
  by induction s;induction r;induction q;reflexivity

-- definition naturality_apdo {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
--   (H : f ~ g) (p : a = a₂)
--   : squareover B vrfl (apdo f p) (apdo g p)
--                       (pathover_idp_of_eq (H a)) (pathover_idp_of_eq (H a₂)) :=
-- by induction p;esimp;exact hrflo

  definition naturality_apdo_eq {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
    (H : f ~ g) (p : a = a₂)
    : apdo f p = concato_eq (eq_concato (H a) (apdo g p)) (H a₂)⁻¹ :=
  begin
    induction p, esimp,
    generalizes [H a, g a], intro ga Ha, induction Ha,
    reflexivity
  end

  theorem con_tr_idp {P : A → Type} {x y : A} (q : x = y) (u : P x) :
    con_tr idp q u = ap (λp, p ▸ u) (idp_con q) :=
  by induction q;reflexivity


end eq
