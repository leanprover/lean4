-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.axioms.ua hott.equiv hott.equiv_precomp
import data.prod data.sigma

open path function prod sigma

-- First, define an axiom free variant of Univalence
definition ua_type := Π (A B : Type), IsEquiv (equiv_path A B)

context
  parameters {ua : ua_type}

  -- TODO base this theorem on UA instead of FunExt.
  -- IsEquiv.postcompose relies on FunExt!
  protected theorem ua_isequiv_postcompose {A B C : Type} {w : A → B} {H0 : IsEquiv w}
      : IsEquiv (@compose C A B w) :=
    !IsEquiv.postcompose

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

  theorem univalence_implies_funext_nondep (A B : Type)
      : Π (f g : A → B), f ∼ g → f ≈ g
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






-- In the following we will proof function extensionality using the univalence axiom
definition funext_from_ua {A : Type} {P : A → Type} (f g : Πx, P x)
    : IsEquiv (@apD10 A P f g) :=
  sorry
