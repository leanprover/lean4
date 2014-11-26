-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.equiv hott.axioms.funext
open path function funext

namespace is_equiv
  context

  --Precomposition of arbitrary functions with f
  definition precomp {A B : Type} (f : A → B) (C : Type) (h : B → C) : A → C := h ∘ f

  --Postcomposition of arbitrary functions with f
  definition postcomp {A B : Type} (f : A → B) (C : Type) (l : C → A) : C → B := f ∘ l

  --Precomposing with an equivalence is an equivalence
  definition precompose [instance] {A B : Type} (f : A → B) [F : funext] [Hf : is_equiv f] (C : Type)
      : is_equiv (precomp f C) :=
    adjointify (precomp f C) (λh, h ∘ f⁻¹)
      (λh, path_forall _ _ (λx, ap h (sect f x)))
      (λg, path_forall _ _ (λy, ap g (retr f y)))

  --Postcomposing with an equivalence is an equivalence
  definition postcompose [instance] {A B : Type} (f : A → B) [F : funext] [Hf : is_equiv f] (C : Type)
      : is_equiv (postcomp f C) :=
    adjointify (postcomp f C) (λl, f⁻¹ ∘ l)
      (λh, path_forall _ _ (λx, retr f (h x)))
      (λg, path_forall _ _ (λy, sect f (g y)))

  --Conversely, if pre- or post-composing with a function is always an equivalence,
  --then that function is also an equivalence.  It's convenient to know
  --that we only need to assume the equivalence when the other type is
  --the domain or the codomain.
  protected definition isequiv_precompose_eq {A B : Type} (f : A → B) (C D : Type)
      (Ceq : is_equiv (precomp f C)) (Deq : is_equiv (precomp f D)) (k : C → D) (h : A → C) :
      k ∘ (inv (precomp f C)) h ≈ (inv (precomp f D)) (k ∘ h) :=
    let invD := inv (precomp f D) in
    let invC := inv (precomp f C) in
    have eq1 : invD (k ∘ h) ≈ k ∘ (invC h),
      from calc invD (k ∘ h) ≈ invD (k ∘ (precomp f C (invC h))) : retr (precomp f C) h
		... ≈ k ∘ (invC h) : !sect,
      eq1⁻¹

  definition isequiv_precompose {A B : Type} (f : A → B) (Aeq : is_equiv (precomp f A))
      (Beq : is_equiv (precomp f B)) : (is_equiv f) :=
    let invA := inv (precomp f A) in
    let invB := inv (precomp f B) in
    let sect' : f ∘ (invA id) ∼ id  := (λx,
      calc f (invA id x) ≈ (f ∘ invA id) x : idp
	... ≈ invB (f ∘ id) x : apD10 (!isequiv_precompose_eq)
	... ≈ invB (precomp f B id) x : idp
	... ≈ x : apD10 (sect (precomp f B) id))
      in
    let retr' : (invA id) ∘ f ∼ id := (λx,
      calc invA id (f x) ≈ precomp f A (invA id) x : idp
	... ≈ x : apD10 (retr (precomp f A) id)) in
    adjointify f (invA id) sect' retr'

  end

end is_equiv

--Bundled versions of the previous theorems
namespace equiv

  definition precompose [F : funext] {A B C : Type} {eqf : A ≃ B}
      : (B → C) ≃ (A → C) :=
    let f := to_fun eqf in
    let Hf := to_is_equiv eqf in
    equiv.mk (is_equiv.precomp f C)
      (@is_equiv.precompose A B f F Hf C)

  definition postcompose [F : funext] {A B C : Type} {eqf : A ≃ B}
      : (C → A) ≃ (C → B) :=
    let f := to_fun eqf in
    let Hf := to_is_equiv eqf in
    equiv.mk (is_equiv.postcomp f C)
      (@is_equiv.postcompose A B f F Hf C)

end equiv
