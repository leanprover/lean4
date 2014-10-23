-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad
-- Ported from Coq HoTT
import .path
open path function

-- Equivalences
-- ------------

definition Sect {A B : Type} (s : A → B) (r : B → A) := Πx : A, r (s x) ≈ x

-- -- TODO: need better means of declaring structures
-- -- TODO: note that Coq allows projections to be declared to be coercions on the fly

-- Structure IsEquiv

inductive IsEquiv [class] {A B : Type} (f : A → B) :=
IsEquiv_mk : Π
  (inv : B → A)
  (retr : Sect inv f)
  (sect : Sect f inv)
  (adj : Πx, retr (f x) ≈ ap f (sect x)),
IsEquiv f


namespace IsEquiv

  definition inv {A B : Type} {f : A → B} (H : IsEquiv f) : B → A :=
    IsEquiv.rec (λinv retr sect adj, inv) H

  -- TODO: note: does not type check without giving the type
  definition retr {A B : Type} {f : A → B} (H : IsEquiv f) : Sect (inv H) f :=
    IsEquiv.rec (λinv retr sect adj, retr) H

  definition sect {A B : Type} {f : A → B} (H : IsEquiv f) : Sect f (inv H) :=
    IsEquiv.rec (λinv retr sect adj, sect) H

  definition adj {A B : Type} {f : A → B} (H : IsEquiv f) :
	     Πx, retr H (f x) ≈ ap f (sect H x) :=
    IsEquiv.rec (λinv retr sect adj, adj) H

end IsEquiv

-- Structure Equiv

inductive Equiv (A B : Type) : Type :=
Equiv_mk : Π
  (equiv_fun : A → B)
  (equiv_isequiv : IsEquiv equiv_fun),
Equiv A B

namespace Equiv

  definition equiv_fun [coercion] {A B : Type} (e : Equiv A B) : A → B :=
    Equiv.rec (λequiv_fun equiv_isequiv, equiv_fun) e

  definition equiv_isequiv [coercion] {A B : Type} (e : Equiv A B) : IsEquiv (equiv_fun e) :=
    Equiv.rec (λequiv_fun equiv_isequiv, equiv_isequiv) e

  infix `≃`:25 := Equiv
  notation e `⁻¹` := IsEquiv.inv e

end Equiv

  -- Some instances and closure properties of equivalences

namespace IsEquiv
  variables {A B C : Type} {f : A → B} {g : B → C} {f' : A → B}

  -- The identity function is an equivalence.

  definition id_closed [instance] : (@IsEquiv A A id) := IsEquiv_mk id (λa, idp) (λa, idp) (λa, idp)

  -- The composition of two equivalences is, again, an equivalence.

  definition comp_closed [instance] (Hf : IsEquiv f) (Hg : IsEquiv g) : (IsEquiv (g ∘ f)) :=
    IsEquiv_mk ((inv Hf) ∘ (inv Hg))
	       (λc, ap g (retr Hf ((inv Hg) c)) ⬝ retr Hg c)
	       (λa, ap (inv Hf) (sect Hg (f a)) ⬝ sect Hf a)
	       (λa, (whiskerL _ (adj Hg (f a))) ⬝
		    (ap_pp g _ _)⁻¹ ⬝
		    ap02 g (concat_A1p (retr Hf) (sect Hg (f a))⁻¹ ⬝
			    (ap_compose (inv Hf) f _ ◾  adj Hf a) ⬝
			    (ap_pp f _ _)⁻¹
			   ) ⬝
		    (ap_compose f g _)⁻¹
	       )

  -- Any function equal to an equivalence is an equivlance as well.
  definition path_closed (Hf : IsEquiv f) (Heq : f ≈ f') : (IsEquiv f') :=
     path.induction_on Heq Hf

  -- Any function pointwise equal to an equivalence is an equivalence as well.
  definition homotopic (Hf : IsEquiv f) (Heq : f ∼ f') : (IsEquiv f') :=
    let sect' := (λ b, (Heq (inv Hf b))⁻¹ ⬝ retr Hf b) in
    let retr' := (λ a, (ap (inv Hf) (Heq a))⁻¹ ⬝ sect Hf a) in
    let adj' := (λ (a : A),
      let ff'a := Heq a in
      let invf := inv Hf in
      let secta := sect Hf a in
      let retrfa := retr Hf (f a) in
      let retrf'a := retr Hf (f' a) in
      have eq1 : _ ≈ _,
        from calc ap f secta ⬝ ff'a
              ≈ retrfa ⬝ ff'a : (ap _ (adj Hf _ ))⁻¹
          ... ≈ ap (f ∘ invf) ff'a ⬝ retrf'a : !concat_A1p⁻¹
          ... ≈ ap f (ap invf ff'a) ⬝ retr Hf (f' a) : {ap_compose invf f ff'a},
      have eq2 : _ ≈ _,
        from calc retrf'a
              ≈ (ap f (ap invf ff'a))⁻¹ ⬝ (ap f secta ⬝ ff'a) : moveL_Vp _ _ _ (eq1⁻¹)
          ... ≈ ap f (ap invf ff'a)⁻¹ ⬝ (ap f secta ⬝ Heq a) : {ap_V invf ff'a}
          ... ≈ ap f (ap invf ff'a)⁻¹ ⬝ (Heq (invf (f a)) ⬝ ap f' secta) : {!concat_Ap}
          ... ≈ (ap f (ap invf ff'a)⁻¹ ⬝ Heq (invf (f a))) ⬝ ap f' secta : {!concat_pp_p⁻¹}
          ... ≈ (ap f ((ap invf ff'a)⁻¹) ⬝ Heq (invf (f a))) ⬝ ap f' secta : {!ap_V⁻¹}
          ... ≈ (Heq (invf (f' a)) ⬝ ap f' ((ap invf ff'a)⁻¹)) ⬝ ap f' secta : {!concat_Ap}
          ... ≈ (Heq (invf (f' a)) ⬝ (ap f' (ap invf ff'a))⁻¹) ⬝ ap f' secta : {!ap_V}
          ... ≈ Heq (invf (f' a)) ⬝ ((ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta) : !concat_pp_p,
      have eq3 : _ ≈ _,
        from calc (Heq (invf (f' a)))⁻¹ ⬝ retr Hf (f' a)
              ≈ (ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta : moveR_Vp _ _ _ eq2
          ... ≈ (ap f' ((ap invf ff'a)⁻¹)) ⬝ ap f' secta : {!ap_V⁻¹}
          ... ≈ ap f' ((ap invf ff'a)⁻¹ ⬝ secta) : !ap_pp⁻¹,
    eq3) in
  IsEquiv_mk (inv Hf) sect' retr' adj'
               
  --TODO: Maybe wait until rewrite rules are available.
  definition inv_closed (Hf : IsEquiv f) : (IsEquiv (inv Hf)) :=
    IsEquiv_mk sorry sorry sorry sorry

  definition cancel_R (Hf : IsEquiv f) (Hgf : IsEquiv (g ∘ f)) : (IsEquiv g) :=
    homotopic (comp_closed (inv_closed Hf) Hgf) (λb, ap g (retr Hf b))

  definition cancel_L (Hg : IsEquiv g) (Hgf : IsEquiv (g ∘ f)) : (IsEquiv f) :=
    homotopic (comp_closed Hgf (inv_closed Hg)) (λa, sect Hg (f a))

  definition transport (P : A → Type) {x y : A} (p : x ≈ y) : (IsEquiv (transport P p)) :=
    IsEquiv_mk (transport P (p⁻¹)) (transport_pV P p) (transport_Vp P p) (transport_pVp P p)

  --Rewrite rules
  section
  variables {Hf : IsEquiv f}
  
  definition moveR_M {x : A} {y : B} (p : x ≈ (inv Hf) y) : (f x ≈ y) :=
    (ap f p) ⬝ (retr Hf y)

  definition moveL_M {x : A} {y : B} (p : (inv Hf) y ≈ x) : (y ≈ f x) :=
    (moveR_M (p⁻¹))⁻¹

  definition moveR_V {x : B} {y : A} (p : x ≈ f y) : (inv Hf) x ≈ y :=
    ap (inv Hf) p ⬝ sect Hf y

  definition moveL_V {x : B} {y : A} (p : f y ≈ x) : y ≈ (inv Hf) x :=
    (moveR_V (p⁻¹))⁻¹
  
  end

end IsEquiv

namespace Equiv

  variables {A B C : Type} (eqf : A ≃ B)

  theorem id : A ≃ A := Equiv_mk id IsEquiv.id_closed

  theorem compose (eqg: B ≃ C) : A ≃ C :=
    Equiv_mk ((equiv_fun eqg) ∘ (equiv_fun eqf))
	     (IsEquiv.comp_closed (equiv_isequiv eqf) (equiv_isequiv eqg))

  check IsEquiv.path_closed

  theorem path_closed (f' : A → B) (Heq : equiv_fun eqf ≈ f') : A ≃ B :=
    Equiv_mk f' (IsEquiv.path_closed (equiv_isequiv eqf) Heq)

  theorem inv_closed : B ≃ A :=
    Equiv_mk (IsEquiv.inv (equiv_isequiv eqf)) (IsEquiv.inv_closed (equiv_isequiv eqf))

  theorem cancel_L {f : A → B} {g : B → C} 
                   (Hf : IsEquiv f) (Hgf : IsEquiv (g ∘ f)) : B ≃ C :=
    Equiv_mk g (IsEquiv.cancel_R _ _)
  
  theorem cancel_R {f : A → B} {g : B → C}
                   (Hg : IsEquiv g) (Hgf : IsEquiv (g ∘ f)) : A ≃ B :=
    Equiv_mk f (!IsEquiv.cancel_L _ _)

  theorem transport (P : A → Type) {x y : A} {p : x ≈ y} : (P x) ≃ (P y) :=
    Equiv_mk (transport P p) (IsEquiv.transport P p)

end Equiv
