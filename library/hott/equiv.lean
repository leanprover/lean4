-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT
import .path .trunc
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
     path.rec_on Heq Hf

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
          ... ≈ ap f (ap invf ff'a) ⬝ retr Hf (f' a) : {ap_compose invf f _},
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
end IsEquiv

namespace IsEquiv

  variables {A B : Type} (f : A → B) (g : B → A)
            (retr : Sect g f) (sect : Sect f g)

  context
  set_option unifier.max_steps 30000
  --To construct an equivalence it suffices to state the proof that the inverse is a quasi-inverse.
  definition adjointify : IsEquiv f :=
    let sect' := (λx, ap g (ap f ((sect x)⁻¹))  ⬝  ap g (retr (f x))  ⬝  sect x) in
    let adj' := (λ (a : A),
      let fgretrfa := ap f (ap g (retr (f a))) in
      let fgfinvsect := ap f (ap g (ap f ((sect a)⁻¹))) in
      let fgfa := f (g (f a)) in
      let retrfa := retr (f a) in
      have eq1 : ap f (sect a) ≈ _,
        from calc ap f (sect a)
              ≈ idp ⬝ ap f (sect a) : !concat_1p⁻¹
          ... ≈ (retr (f a) ⬝ (retr (f a)⁻¹)) ⬝ ap f (sect a) : {!concat_pV⁻¹}
          ... ≈ ((retr (fgfa))⁻¹ ⬝ ap (f ∘ g) (retr (f a))) ⬝ ap f (sect a) : {!concat_pA1⁻¹}
          ... ≈ ((retr (fgfa))⁻¹ ⬝ fgretrfa) ⬝ ap f (sect a) : {ap_compose g f _}
          ... ≈ (retr (fgfa))⁻¹ ⬝ (fgretrfa ⬝ ap f (sect a)) : !concat_pp_p,
      have eq2 : ap f (sect a) ⬝ idp ≈ (retr (fgfa))⁻¹ ⬝ (fgretrfa ⬝ ap f (sect a)),
        from !concat_p1 ▹ eq1,
      have eq3 : idp ≈ _,
        from calc idp
              ≈ (ap f (sect a))⁻¹ ⬝ ((retr (fgfa))⁻¹ ⬝ (fgretrfa ⬝ ap f (sect a))) : moveL_Vp _ _ _ eq2
          ... ≈ (ap f (sect a)⁻¹ ⬝ (retr (fgfa))⁻¹) ⬝ (fgretrfa ⬝ ap f (sect a)) : !concat_p_pp
          ... ≈ (ap f ((sect a)⁻¹) ⬝ (retr (fgfa))⁻¹) ⬝ (fgretrfa ⬝ ap f (sect a)) : {!ap_V⁻¹}
          ... ≈ ((ap f ((sect a)⁻¹) ⬝ (retr (fgfa))⁻¹) ⬝ fgretrfa) ⬝ ap f (sect a) : !concat_p_pp
          ... ≈ ((retrfa⁻¹ ⬝ ap (f ∘ g) (ap f ((sect a)⁻¹))) ⬝ fgretrfa) ⬝ ap f (sect a) : {!concat_pA1⁻¹}
          ... ≈ ((retrfa⁻¹ ⬝ fgfinvsect) ⬝ fgretrfa) ⬝ ap f (sect a) : {ap_compose g f _}
          ... ≈ (retrfa⁻¹ ⬝ (fgfinvsect ⬝ fgretrfa)) ⬝ ap f (sect a) : {!concat_p_pp⁻¹}
          ... ≈ retrfa⁻¹ ⬝ ap f (ap g (ap f ((sect a)⁻¹)) ⬝ ap g (retr (f a))) ⬝ ap f (sect a) : {!ap_pp⁻¹}
          ... ≈ retrfa⁻¹ ⬝ (ap f (ap g (ap f ((sect a)⁻¹)) ⬝ ap g (retr (f a))) ⬝ ap f (sect a)) : !concat_p_pp⁻¹
          ... ≈ retrfa⁻¹ ⬝ ap f ((ap g (ap f ((sect a)⁻¹)) ⬝ ap g (retr (f a))) ⬝ sect a) : {!ap_pp⁻¹},
      have eq4 : retr (f a) ≈ ap f ((ap g (ap f ((sect a)⁻¹)) ⬝ ap g (retr (f a))) ⬝ sect a),
        from moveR_M1 _ _ eq3,
      eq4) in
    IsEquiv_mk g retr sect' adj'
  end
end IsEquiv

namespace IsEquiv
  variables {A B: Type} {f : A → B} (Hf : IsEquiv f)

  --The inverse of an equivalence is, again, an equivalence.
  definition inv_closed : (IsEquiv (inv Hf)) :=
    adjointify (inv Hf) f (sect Hf) (retr Hf)

end IsEquiv

namespace IsEquiv
  variables {A B C : Type} {f : A → B} {g : B → C} {f' : A → B}

  definition cancel_R (Hf : IsEquiv f) (Hgf : IsEquiv (g ∘ f)) : (IsEquiv g) :=
    homotopic (comp_closed (inv_closed Hf) Hgf) (λb, ap g (retr Hf b))

  definition cancel_L (Hg : IsEquiv g) (Hgf : IsEquiv (g ∘ f)) : (IsEquiv f) :=
    homotopic (comp_closed Hgf (inv_closed Hg)) (λa, sect Hg (f a))

  --Transporting is an equivalence
  definition transport [instance] (P : A → Type) {x y : A} (p : x ≈ y) : (IsEquiv (transport P p)) :=
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

  definition contr (HA: Contr A) : (Contr B) :=
    Contr.Contr_mk (f (center HA)) (λb, moveR_M (contr HA (inv Hf b)))

  end

  --If pre- or post-composing with a function is always an equivalence,
  --then that function is also an equivalence.  It's convenient to know
  --that we only need to assume the equivalence when the other type is
  --the domain or the codomain.
  section

  definition precomp (C : Type) (h : B → C) : A → C := h ∘ f

  definition inv_precomp (C D : Type) (Ceq : IsEquiv (precomp C))
      (Deq : IsEquiv (@precomp A B f D)) (k : C → D) (h : A → C) :
      k ∘ (inv Ceq) h ≈ (inv Deq) (k ∘ h) :=
    have eq1 : (inv Deq) (k ∘ h) ≈ k ∘ ((inv Ceq) h),
      from calc (inv Deq) (k ∘ h) ≈ (inv Deq) (k ∘ (precomp C ((inv Ceq) h))) : retr Ceq h
                ... ≈ k ∘ ((inv Ceq) h) : !sect,
      eq1⁻¹

  definition isequiv_precompose (Aeq : IsEquiv (@precomp A B f A))
      (Beq : IsEquiv (@precomp A B f B)) : (IsEquiv f) :=
    let sect' : Sect ((inv Aeq) id) f := (λx,
      calc f (inv Aeq id x) ≈ (f ∘ (inv Aeq) id) x : idp
        ... ≈ (inv Beq) (f ∘ id) x : apD10 (!inv_precomp)
        ... ≈ (inv Beq) (@precomp A B f B id) x : idp
        ... ≈ x : apD10 (sect Beq id))
      in
    let retr' : Sect f ((inv Aeq) id) := (λx,
      calc inv Aeq id (f x) ≈ @precomp A B f A ((inv Aeq) id) x : idp
        ... ≈ x : apD10 (retr Aeq id)) in
    adjointify f ((inv Aeq) id) sect' retr'

  end

end IsEquiv

namespace Equiv
  variables {A B C : Type} (eqf : A ≃ B)

  definition id : A ≃ A := Equiv_mk id IsEquiv.id_closed

  theorem compose (eqg: B ≃ C) : A ≃ C :=
    Equiv_mk ((equiv_fun eqg) ∘ (equiv_fun eqf))
             (IsEquiv.comp_closed (equiv_isequiv eqf) (equiv_isequiv eqg))

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

  theorem contr_closed (HA: Contr A) : (Contr B) :=
    @IsEquiv.contr A B (equiv_fun eqf) (equiv_isequiv eqf) HA

end Equiv

namespace Equiv
  variables {A B : Type} {HA : Contr A} {HB : Contr B}

  --Each two contractible types are equivalent.
  definition contr_contr : A ≃ B :=
    Equiv_mk
      (λa, center HB)
      (IsEquiv.adjointify (λa, center HB) (λb, center HA) 
        (contr HB) (contr HA))

end Equiv
