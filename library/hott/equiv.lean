-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
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
mk : Π
  (inv : B → A)
  (retr : Sect inv f)
  (sect : Sect f inv)
  (adj : Πx, retr (f x) ≈ ap f (sect x)),
IsEquiv f

namespace IsEquiv

  definition inv {A B : Type} (f : A → B) [H : IsEquiv f] : B → A :=
    IsEquiv.rec (λinv retr sect adj, inv) H

  -- TODO: note: does not type check without giving the type
  definition retr {A B : Type} (f : A → B) [H : IsEquiv f] : Sect (inv f) f :=
    IsEquiv.rec (λinv retr sect adj, retr) H

  definition sect {A B : Type} (f : A → B) [H : IsEquiv f] : Sect f (inv f) :=
    IsEquiv.rec (λinv retr sect adj, sect) H

  definition adj {A B : Type} (f : A → B) [H : IsEquiv f] :
             Πx, retr f (f x) ≈ ap f (sect f x) :=
    IsEquiv.rec (λinv retr sect adj, adj) H

  postfix `⁻¹` := inv

end IsEquiv

-- Structure Equiv

inductive Equiv (A B : Type) : Type :=
mk : Π
  (equiv_fun : A → B)
  (equiv_isequiv : IsEquiv equiv_fun),
Equiv A B

namespace Equiv

  definition equiv_fun [coercion] {A B : Type} (e : Equiv A B) : A → B :=
    Equiv.rec (λequiv_fun equiv_isequiv, equiv_fun) e

  definition equiv_isequiv [instance] {A B : Type} (e : Equiv A B) : IsEquiv (equiv_fun e) :=
    Equiv.rec (λequiv_fun equiv_isequiv, equiv_isequiv) e

  infix `≃`:25 := Equiv

end Equiv

  -- Some instances and closure properties of equivalences

namespace IsEquiv
  variables {A B C : Type} {f : A → B} {g : B → C} {f' : A → B}

  -- The identity function is an equivalence.

  definition id_closed [instance] : (@IsEquiv A A id) := IsEquiv.mk id (λa, idp) (λa, idp) (λa, idp)

  -- The composition of two equivalences is, again, an equivalence.

  definition comp_closed [instance] (Hf : IsEquiv f) (Hg : IsEquiv g) : (IsEquiv (g ∘ f)) :=
    IsEquiv.mk ((inv f) ∘ (inv g))
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
  definition path_closed (Hf : IsEquiv f) (Heq : f ≈ f') : (IsEquiv f') :=
     path.rec_on Heq Hf

  -- Any function pointwise equal to an equivalence is an equivalence as well.
  definition homotopic (Hf : IsEquiv f) (Heq : f ∼ f') : (IsEquiv f') :=
    let sect' := (λ b, (Heq (inv f b))⁻¹ ⬝ retr f b) in
    let retr' := (λ a, (ap (inv f) (Heq a))⁻¹ ⬝ sect f a) in
    let adj' := (λ (a : A),
      let ff'a := Heq a in
      let invf := inv f in
      let secta := sect f a in
      let retrfa := retr f (f a) in
      let retrf'a := retr f (f' a) in
      have eq1 : _ ≈ _,
        from calc ap f secta ⬝ ff'a
              ≈ retrfa ⬝ ff'a : (ap _ (adj f _ ))⁻¹
          ... ≈ ap (f ∘ invf) ff'a ⬝ retrf'a : !concat_A1p⁻¹
          ... ≈ ap f (ap invf ff'a) ⬝ retr f (f' a) : {ap_compose invf f _},
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
        from calc (Heq (invf (f' a)))⁻¹ ⬝ retr f (f' a)
              ≈ (ap f' (ap invf ff'a))⁻¹ ⬝ ap f' secta : moveR_Vp _ _ _ eq2
          ... ≈ (ap f' ((ap invf ff'a)⁻¹)) ⬝ ap f' secta : {!ap_V⁻¹}
          ... ≈ ap f' ((ap invf ff'a)⁻¹ ⬝ secta) : !ap_pp⁻¹,
    eq3) in
  IsEquiv.mk (inv f) sect' retr' adj'
end IsEquiv

namespace IsEquiv

  variables {A B : Type} (f : A → B) (g : B → A)
            (ret : Sect g f) (sec : Sect f g)

  context
  set_option unifier.max_steps 30000
  --To construct an equivalence it suffices to state the proof that the inverse is a quasi-inverse.
  definition adjointify : IsEquiv f :=
    let sect' := (λx, ap g (ap f (inverse (sec x))) ⬝ ap g (ret (f x)) ⬝ sec x) in
    let adj' := (λ (a : A),
      let fgretrfa := ap f (ap g (ret (f a))) in
      let fgfinvsect := ap f (ap g (ap f ((sec a)⁻¹))) in
      let fgfa := f (g (f a)) in
      let retrfa := ret (f a) in
      have eq1 : ap f (sec a) ≈ _,
        from calc ap f (sec a)
              ≈ idp ⬝ ap f (sec a) : !concat_1p⁻¹
          ... ≈ (ret (f a) ⬝ (ret (f a)⁻¹)) ⬝ ap f (sec a) : {!concat_pV⁻¹}
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
      eq4) in
    IsEquiv.mk g ret sect' adj'
  end
end IsEquiv

namespace IsEquiv
  variables {A B: Type} (f : A → B)
  
  --The inverse of an equivalence is, again, an equivalence.
  definition inv_closed [instance] [Hf : IsEquiv f] : (IsEquiv (inv f)) :=
    adjointify (inv f) f (sect f) (retr f)

end IsEquiv

namespace IsEquiv
  variables {A : Type}
  section
  variables {B C : Type} (f : A → B) {f' : A → B} [Hf : IsEquiv f]
  include Hf

  definition cancel_R (g : B → C) [Hgf : IsEquiv (g ∘ f)] : (IsEquiv g) :=
    homotopic (comp_closed !inv_closed Hgf) (λb, ap g (retr f b))

  definition cancel_L (g : C → A) [Hgf : IsEquiv (f ∘ g)] : (IsEquiv g) :=
    homotopic (comp_closed Hgf !inv_closed) (λa, sect f (g a))

  --Rewrite rules
  definition moveR_M {x : A} {y : B} (p : x ≈ (inv f) y) : (f x ≈ y) :=
    (ap f p) ⬝ (retr f y)

  definition moveL_M {x : A} {y : B} (p : (inv f) y ≈ x) : (y ≈ f x) :=
    (moveR_M f (p⁻¹))⁻¹

  definition moveR_V {x : B} {y : A} (p : x ≈ f y) : (inv f) x ≈ y :=
    ap (inv f) p ⬝ sect f y

  definition moveL_V {x : B} {y : A} (p : f y ≈ x) : y ≈ (inv f) x :=
    (moveR_V f (p⁻¹))⁻¹

  definition ap_closed [instance] (x y : A) : IsEquiv (ap f) := 
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
    let eq1 := (apD df (sect f x)) in
    calc equiv_rect f P df (f x)
          ≈ transport P (retr f (f x)) (df (f⁻¹ (f x))) : idp
      ... ≈ transport P (ap f (sect f x)) (df (f⁻¹ (f x))) : adj f
      ... ≈ transport (P ∘ f) (sect f x) (df (f⁻¹ (f x))) : transport_compose
      ... ≈ df x : eq1

  end

  --Transporting is an equivalence
  definition transport [instance] (P : A → Type) {x y : A} (p : x ≈ y) : (IsEquiv (transport P p)) :=
    IsEquiv.mk (transport P (p⁻¹)) (transport_pV P p) (transport_Vp P p) (transport_pVp P p)

end IsEquiv

namespace Equiv
  context
  parameters {A B C : Type} (eqf : A ≃ B)

  private definition f : A → B := equiv_fun eqf
  private definition Hf : IsEquiv f := equiv_isequiv eqf

  protected definition id : A ≃ A := Equiv.mk id IsEquiv.id_closed

  theorem compose (eqg: B ≃ C) : A ≃ C :=
    Equiv.mk ((equiv_fun eqg) ∘ f)
             (IsEquiv.comp_closed Hf (equiv_isequiv eqg))

  theorem path_closed (f' : A → B) (Heq : equiv_fun eqf ≈ f') : A ≃ B :=
    Equiv.mk f' (IsEquiv.path_closed Hf Heq)

  theorem inv_closed : B ≃ A :=
    Equiv.mk (IsEquiv.inv f) !IsEquiv.inv_closed

  theorem cancel_R {g : B → C} (Hgf : IsEquiv (g ∘ f)) : B ≃ C :=
    Equiv.mk g (IsEquiv.cancel_R f _)

  theorem cancel_L {g : C → A} (Hgf : IsEquiv (f ∘ g)) : C ≃ A :=
    Equiv.mk g (IsEquiv.cancel_L f _)

  theorem transport (P : A → Type) {x y : A} {p : x ≈ y} : (P x) ≃ (P y) :=
    Equiv.mk (transport P p) (IsEquiv.transport P p)

  end

  -- calc enviroment
  -- Note: Calculating with substitutions needs univalence
  calc_trans compose
  calc_refl id
  calc_symm inv_closed

end Equiv
