-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT
import .path
open path function

-- Equivalences
-- ------------

-- This is our definition of equivalence. In the HoTT-book it's called
-- ihae (half-adjoint equivalence).
structure is_equiv [class] {A B : Type} (f : A → B) :=
  (inv : B → A)
  (retr : (f ∘ inv) ∼ id)
  (sect : (inv ∘ f) ∼ id)
  (adj : Πx, retr (f x) ≈ ap f (sect x))


-- A more bundled version of equivalence to calculate with
structure equiv (A B : Type) :=
  (to_fun : A → B)
  (to_is_equiv : is_equiv to_fun)

 -- Some instances and closure properties of equivalences
namespace is_equiv

  postfix `⁻¹` := inv

  variables {A B C : Type} (f : A → B) (g : B → C) {f' : A → B}

  -- The identity function is an equivalence.
  definition id_is_equiv : (@is_equiv A A id) := is_equiv.mk id (λa, idp) (λa, idp) (λa, idp)

  -- The composition of two equivalences is, again, an equivalence.
  protected definition compose [Hf : is_equiv f] [Hg : is_equiv g] : (is_equiv (g ∘ f)) :=
    is_equiv.mk ((inv f) ∘ (inv g))
               (λc, ap g (retr f (g⁻¹ c)) ⬝ retr g c)
               (λa, ap (inv f) (sect g (f a)) ⬝ sect f a)
               (λa, (whiskerL _ (adj g (f a))) ⬝
                    (ap_pp g _ _)⁻¹ ⬝
                    ap02 g (concat_A1p (retr f) (sect g (f a))⁻¹ ⬝
                            (ap_compose (inv f) f _ ◾  adj f a) ⬝
                            (ap_pp f _ _)⁻¹
                           ) ⬝
                    (ap_compose f g _)⁻¹
               )

  -- Any function equal to an equivalence is an equivlance as well.
  definition path_closed [Hf : is_equiv f] (Heq : f ≈ f') : (is_equiv f') :=
     path.rec_on Heq Hf

  -- Any function pointwise equal to an equivalence is an equivalence as well.
  definition homotopy_closed [Hf : is_equiv f] (Hty : f ∼ f') : (is_equiv f') :=
    let sect' := (λ b, (Hty (inv f b))⁻¹ ⬝ retr f b) in
    let retr' := (λ a, (ap (inv f) (Hty a))⁻¹ ⬝ sect f a) in
    let adj' := (λ (a : A),
      let ff'a := Hty a in
      let invf := inv f in
      let secta := sect f a in
      let retrfa := retr f (f a) in
      let retrf'a := retr f (f' a) in
      have eq1 : _ ≈ _,
        from calc ap f secta ⬝ ff'a
              ≈ retrfa ⬝ ff'a : ap _ (@adj _ _ f _ _)
          ... ≈ ap (f ∘ invf) ff'a ⬝ retrf'a : concat_A1p
          ... ≈ ap f (ap invf ff'a) ⬝ retrf'a : ap_compose invf f,
      have eq2 : _ ≈ _,
        from calc retrf'a
              ≈ (ap f (ap invf ff'a))⁻¹ ⬝ (ap f secta ⬝ ff'a) : moveL_Vp _ _ _ (eq1⁻¹)
          ... ≈ ap f (ap invf ff'a)⁻¹ ⬝ (ap f secta ⬝ Hty a) : ap_V invf ff'a
          ... ≈ ap f (ap invf ff'a)⁻¹ ⬝ (Hty (invf (f a)) ⬝ ap f' secta) : concat_Ap
          ... ≈ (ap f (ap invf ff'a)⁻¹ ⬝ Hty (invf (f a))) ⬝ ap f' secta : concat_pp_p
          ... ≈ (ap f ((ap invf ff'a)⁻¹) ⬝ Hty (invf (f a))) ⬝ ap f' secta : ap_V
          ... ≈ (Hty (invf (f' a)) ⬝ ap f' ((ap invf ff'a)⁻¹)) ⬝ ap f' secta : concat_Ap
          ... ≈ (Hty (invf (f' a)) ⬝ (ap f' (ap invf ff'a))⁻¹) ⬝ ap f' secta : ap_V
          ... ≈ Hty (invf (f' a)) ⬝ ((ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta) : concat_pp_p,
      have eq3 : _ ≈ _,
        from calc (Hty (invf (f' a)))⁻¹ ⬝ retrf'a
              ≈ (ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta : moveR_Vp _ _ _ eq2
          ... ≈ (ap f' ((ap invf ff'a)⁻¹)) ⬝ ap f' secta : ap_V
          ... ≈ ap f' ((ap invf ff'a)⁻¹ ⬝ secta) : ap_pp,
    eq3) in
  is_equiv.mk (inv f) sect' retr' adj'
end is_equiv

namespace is_equiv
  context
  parameters {A B : Type} (f : A → B) (g : B → A)
            (ret : f ∘ g ∼ id) (sec : g ∘ f ∼ id)

  definition adjointify_sect' : g ∘ f ∼ id :=
    (λx, ap g (ap f (inverse (sec x))) ⬝ ap g (ret (f x)) ⬝ sec x)

  definition adjointify_adj' : Π (x : A), ret (f x) ≈ ap f (adjointify_sect' x) :=
    (λ (a : A),
      let fgretrfa := ap f (ap g (ret (f a))) in
      let fgfinvsect := ap f (ap g (ap f ((sec a)⁻¹))) in
      let fgfa := f (g (f a)) in
      let retrfa := ret (f a) in
      have eq1 : ap f (sec a) ≈ _,
        from calc ap f (sec a)
              ≈ idp ⬝ ap f (sec a) : !concat_1p⁻¹
          ... ≈ (ret (f a) ⬝ (ret (f a)⁻¹)) ⬝ ap f (sec a) : concat_pV
          ... ≈ ((ret (fgfa))⁻¹ ⬝ ap (f ∘ g) (ret (f a))) ⬝ ap f (sec a) : {!concat_pA1⁻¹}
          ... ≈ ((ret (fgfa))⁻¹ ⬝ fgretrfa) ⬝ ap f (sec a) : {ap_compose g f _}
          ... ≈ (ret (fgfa))⁻¹ ⬝ (fgretrfa ⬝ ap f (sec a)) : !concat_pp_p,
      have eq2 : ap f (sec a) ⬝ idp ≈ (ret fgfa)⁻¹ ⬝ (fgretrfa ⬝ ap f (sec a)),
        from !concat_p1 ⬝ eq1,
      have eq3 : idp ≈ _,
        from calc idp
              ≈ (ap f (sec a))⁻¹ ⬝ ((ret fgfa)⁻¹ ⬝ (fgretrfa ⬝ ap f (sec a))) : moveL_Vp _ _ _ eq2
          ... ≈ (ap f (sec a)⁻¹ ⬝ (ret fgfa)⁻¹) ⬝ (fgretrfa ⬝ ap f (sec a)) : !concat_p_pp
          ... ≈ (ap f ((sec a)⁻¹) ⬝ (ret fgfa)⁻¹) ⬝ (fgretrfa ⬝ ap f (sec a)) : {!ap_V⁻¹}
          ... ≈ ((ap f ((sec a)⁻¹) ⬝ (ret fgfa)⁻¹) ⬝ fgretrfa) ⬝ ap f (sec a) : !concat_p_pp
          ... ≈ ((retrfa⁻¹ ⬝ ap (f ∘ g) (ap f ((sec a)⁻¹))) ⬝ fgretrfa) ⬝ ap f (sec a) : {!concat_pA1⁻¹}
          ... ≈ ((retrfa⁻¹ ⬝ fgfinvsect) ⬝ fgretrfa) ⬝ ap f (sec a) : {ap_compose g f _}
          ... ≈ (retrfa⁻¹ ⬝ (fgfinvsect ⬝ fgretrfa)) ⬝ ap f (sec a) : {!concat_p_pp⁻¹}
          ... ≈ retrfa⁻¹ ⬝ ap f (ap g (ap f ((sec a)⁻¹)) ⬝ ap g (ret (f a))) ⬝ ap f (sec a) : {!ap_pp⁻¹}
          ... ≈ retrfa⁻¹ ⬝ (ap f (ap g (ap f ((sec a)⁻¹)) ⬝ ap g (ret (f a))) ⬝ ap f (sec a)) : !concat_p_pp⁻¹
          ... ≈ retrfa⁻¹ ⬝ ap f ((ap g (ap f ((sec a)⁻¹)) ⬝ ap g (ret (f a))) ⬝ sec a) : {!ap_pp⁻¹},
      have eq4 : ret (f a) ≈ ap f ((ap g (ap f ((sec a)⁻¹)) ⬝ ap g (ret (f a))) ⬝ sec a),
        from moveR_M1 _ _ eq3,
      eq4)

  definition adjointify : is_equiv f :=
    is_equiv.mk g ret adjointify_sect' adjointify_adj'

  end
end is_equiv

namespace is_equiv
  variables {A B: Type} (f : A → B)

  --The inverse of an equivalence is, again, an equivalence.
  definition inv_closed [instance] [Hf : is_equiv f] : (is_equiv (inv f)) :=
    adjointify (inv f) f (sect f) (retr f)

end is_equiv

namespace is_equiv
  variables {A : Type}
  section
  variables {B C : Type} (f : A → B) {f' : A → B} [Hf : is_equiv f]
  include Hf

  definition cancel_R (g : B → C) [Hgf : is_equiv (g ∘ f)] : (is_equiv g) :=
    have Hfinv [visible] : is_equiv (f⁻¹), from inv_closed f,
    @homotopy_closed _ _ _ _ (compose (f⁻¹) (g ∘ f)) (λb, ap g (@retr _ _ f _ b))

  definition cancel_L (g : C → A) [Hgf : is_equiv (f ∘ g)] : (is_equiv g) :=
    have Hfinv [visible] : is_equiv (f⁻¹), from inv_closed f,
    @homotopy_closed _ _ _ _ (compose (f ∘ g) (f⁻¹)) (λa, sect f (g a))

  --Rewrite rules
  definition moveR_M {x : A} {y : B} (p : x ≈ (inv f) y) : (f x ≈ y) :=
    (ap f p) ⬝ (@retr _ _ f _ y)

  definition moveL_M {x : A} {y : B} (p : (inv f) y ≈ x) : (y ≈ f x) :=
    (moveR_M f (p⁻¹))⁻¹

  definition moveR_V {x : B} {y : A} (p : x ≈ f y) : (inv f) x ≈ y :=
    ap (f⁻¹) p ⬝ sect f y

  definition moveL_V {x : B} {y : A} (p : f y ≈ x) : y ≈ (inv f) x :=
    (moveR_V f (p⁻¹))⁻¹

  definition ap_closed [instance] (x y : A) : is_equiv (ap f) :=
    adjointify (ap f)
      (λq, (inverse (sect f x)) ⬝ ap (f⁻¹) q ⬝ sect f y)
      (λq, !ap_pp
        ⬝ whiskerR !ap_pp _
        ⬝ ((!ap_V ⬝ inverse2 ((adj f _)⁻¹))
          ◾ (inverse (ap_compose (f⁻¹) f _))
          ◾ (adj f _)⁻¹)
        ⬝ concat_pA1_p (retr f) _ _
        ⬝ whiskerR !concat_Vp _
        ⬝ !concat_1p)
      (λp, whiskerR (whiskerL _ ((ap_compose f (f⁻¹) _)⁻¹)) _
        ⬝ concat_pA1_p (sect f) _ _
        ⬝ whiskerR !concat_Vp _
        ⬝ !concat_1p)

  -- The function equiv_rect says that given an equivalence f : A → B,
  -- and a hypothesis from B, one may always assume that the hypothesis
  -- is in the image of e.

  -- In fibrational terms, if we have a fibration over B which has a section
  -- once pulled back along an equivalence f : A → B, then it has a section
  -- over all of B.

  definition equiv_rect (P : B -> Type) :
      (Πx, P (f x)) → (Πy, P y) :=
    (λg y, path.transport _ (retr f y) (g (f⁻¹ y)))

  definition equiv_rect_comp (P : B → Type)
      (df : Π (x : A), P (f x)) (x : A) : equiv_rect f P df (f x) ≈ df x :=
    calc equiv_rect f P df (f x)
          ≈ transport P (retr f (f x)) (df (f⁻¹ (f x))) : idp
      ... ≈ transport P (ap f (sect f x)) (df (f⁻¹ (f x))) : adj f
      ... ≈ transport (P ∘ f) (sect f x) (df (f⁻¹ (f x))) : transport_compose
      ... ≈ df x : apD df (sect f x)

  end

  --Transporting is an equivalence
  protected definition transport [instance] (P : A → Type) {x y : A} (p : x ≈ y) : (is_equiv (transport P p)) :=
    is_equiv.mk (transport P (p⁻¹)) (transport_pV P p) (transport_Vp P p) (transport_pVp P p)

end is_equiv

namespace equiv

  instance [persistent] to_is_equiv

  infix `≃`:25 := equiv

  context
  parameters {A B C : Type} (eqf : A ≃ B)

  private definition f : A → B := to_fun eqf
  private definition Hf [instance] : is_equiv f := to_is_equiv eqf

  protected definition refl : A ≃ A := equiv.mk id is_equiv.id_is_equiv

  theorem trans (eqg: B ≃ C) : A ≃ C :=
    equiv.mk ((to_fun eqg) ∘ f)
             (is_equiv.compose f (to_fun eqg))

  theorem path_closed (f' : A → B) (Heq : to_fun eqf ≈ f') : A ≃ B :=
    equiv.mk f' (is_equiv.path_closed f Heq)

  theorem symm : B ≃ A :=
    equiv.mk (is_equiv.inv f) !is_equiv.inv_closed

  theorem cancel_R (g : B → C) [Hgf : is_equiv (g ∘ f)] : B ≃ C :=
    equiv.mk g (is_equiv.cancel_R f _)

  theorem cancel_L (g : C → A) [Hgf : is_equiv (f ∘ g)] : C ≃ A :=
    equiv.mk g (is_equiv.cancel_L f _)

  protected theorem transport (P : A → Type) {x y : A} {p : x ≈ y} : (P x) ≃ (P y) :=
    equiv.mk (transport P p) (is_equiv.transport P p)

  end

  context
  parameters {A B : Type} (eqf eqg : A ≃ B)

  private definition Hf [instance] : is_equiv (to_fun eqf) := to_is_equiv eqf
  private definition Hg [instance] : is_equiv (to_fun eqg) := to_is_equiv eqg

  --We need this theorem for the funext_from_ua proof
  theorem inv_eq (p : eqf ≈ eqg)
      : is_equiv.inv (to_fun eqf) ≈ is_equiv.inv (to_fun eqg) :=
    path.rec_on p idp

  end

  -- calc enviroment
  -- Note: Calculating with substitutions needs univalence
  calc_trans trans
  calc_refl refl
  calc_symm symm

end equiv
