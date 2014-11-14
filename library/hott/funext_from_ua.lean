-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.equiv hott.funext_varieties
import data.prod data.sigma data.unit

open path function prod sigma truncation Equiv IsEquiv unit

definition isequiv_path {A B : Type} (H : A ≈ B) :=
  (@IsEquiv.transport Type (λX, X) A B H)


definition equiv_path {A B : Type} (H : A ≈ B) : A ≃ B :=
  Equiv.mk _ (isequiv_path H)

-- First, define an axiom free variant of Univalence
definition ua_type := Π (A B : Type), IsEquiv (@equiv_path A B)

context
  parameters {ua : ua_type.{1}}

  -- TODO base this theorem on UA instead of FunExt.
  -- IsEquiv.postcompose relies on FunExt!
  protected theorem ua_isequiv_postcompose {A B C : Type.{1}} {w : A → B} {H0 : IsEquiv w}
      : IsEquiv (@compose C A B w)
    := IsEquiv.adjointify (@compose C A B w)
         (@compose C B A (IsEquiv.inv w))
         (λ (x : C → B),
           let w' := Equiv.mk w H0 in
           have foo : Equiv.equiv_fun w' ≈ w,
             from idp,
           have eqretr : equiv_path (equiv_path⁻¹ w') ≈ w',
             from (@retr _ _ (@equiv_path A B) (ua A B) w'),
           have eqinv : A ≈ B,
             from (@inv _ _ (@equiv_path A B) (ua A B) w'),
           have thoseeqs [visible] : Π (p : A ≈ B), IsEquiv (Equiv.equiv_fun (equiv_path p)),
             from (λp, Equiv.equiv_isequiv (equiv_path p)),
           have eqp : Π (p : A ≈ B) (x : C → B), equiv_path p ∘ ((equiv_path p)⁻¹ ∘ x) ≈ x,
             from (λ p,
               (@path.rec_on Type.{1} A
                 (λ B' p', Π (x' : C → B'), (@equiv_path A B' p') ∘ ((equiv_path p')⁻¹ ∘ x') ≈ x')
                 B p (λ x', idp))
               ),
           --have eqfin : equiv_path eqinv ∘ ((equiv_path eqinv)⁻¹ eqinv ∘ x) ≈ x,
           --  from eqp eqinv,
           sorry
         )
         (λ x, sorry)
exit
  -- We are ready to prove functional extensionality,
  -- starting with the naive non-dependent version.
  protected definition diagonal [reducible] (B : Type) : Type
    := Σ xy : B × B, pr₁ xy ≈ pr₂ xy

  protected definition isequiv_src_compose {A B C : Type}
      : @IsEquiv (A → diagonal B)
                 (A → B)
                 (compose (pr₁ ∘ dpr1))
    := @ua_isequiv_postcompose _ _ _ (pr₁ ∘ dpr1)
        (IsEquiv.adjointify (pr₁ ∘ dpr1)
          (λ x, dpair (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, path.rec_on p idp))))

  protected definition isequiv_tgt_compose {A B C : Type}
      : @IsEquiv (A → diagonal B)
                 (A → B)
                 (compose (pr₂ ∘ dpr1))
    := @ua_isequiv_postcompose _ _ _ (pr2 ∘ dpr1)
        (IsEquiv.adjointify (pr2 ∘ dpr1)
          (λ x, dpair (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, path.rec_on p idp))))

  theorem ua_implies_funext_nondep {A B : Type}
      : Π {f g : A → B}, f ∼ g → f ≈ g
    := (λ (f g : A → B) (p : f ∼ g),
          let d := λ (x : A), dpair (f x , f x) idp in
          let e := λ (x : A), dpair (f x , g x) (p x) in
          let precomp1 :=  compose (pr₁ ∘ dpr1) in
          have equiv1 [visible] : IsEquiv precomp1,
            from @isequiv_src_compose A B (diagonal B),
          have equiv2 [visible] : Π x y, IsEquiv (ap precomp1),
            from IsEquiv.ap_closed precomp1,
          have H' : Π (x y : A → diagonal B),
              pr₁ ∘ dpr1 ∘ x ≈ pr₁ ∘ dpr1 ∘ y → x ≈ y,
            from (λ x y, IsEquiv.inv (ap precomp1)),
          have eq2 : pr₁ ∘ dpr1 ∘ d ≈ pr₁ ∘ dpr1 ∘ e,
            from idp,
          have eq0 : d ≈ e,
            from H' d e eq2,
          have eq1 : (pr₂ ∘ dpr1) ∘ d ≈ (pr₂ ∘ dpr1) ∘ e,
            from ap _ eq0,
          eq1
       )

end

context
  universe l
  parameters {ua1 ua2 : ua_type.{1}}

  -- Now we use this to prove weak funext, which as we know
  -- implies (with dependent eta) also the strong dependent funext.
  theorem ua_implies_weak_funext : weak_funext
    := (λ A P allcontr,
          let U := (λ (x : A), unit) in
          have pequiv : Πx, P x ≃ U x,
            from (λ x, @equiv_contr_unit (P x) (allcontr x)),
          have psim : Πx, P x ≈ U x,
            from (λ x, @IsEquiv.inv _ _
              (@equiv_path.{1} (P x) (U x)) (ua1 (P x) (U x)) (pequiv x)),
          have p : P ≈ U,
            from ua_implies_funext_nondep psim,
          have tU' : is_contr (A → unit),
            from is_contr.mk (λ x, ⋆)
              (λ f, ua_implies_funext_nondep
                (λ x, unit.rec_on (f x) idp)),
          have tU : is_contr (Πx, U x),
            from tU',
          have tlast : is_contr (Πx, P x),
            from path.transport _ (p⁻¹) tU,
          tlast
       )

end

-- In the following we will proof function extensionality using the univalence axiom
-- TODO: check out why I have to generalize on A and P here
definition ua_implies_funext_type {ua : ua_type.{1}} : @funext_type :=
  (λ A P, weak_funext_implies_funext (@ua_implies_weak_funext ua))
