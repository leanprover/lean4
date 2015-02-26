/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: equiv_precomp
Author: Jakob von Raumer

Ported from Coq HoTT
-/

-- This file is nowhere used. Do we want to keep it?
open eq function funext

namespace is_equiv
  context

  --Precomposition of arbitrary functions with f
  definition precompose {A B : Type} (f : A → B) (C : Type) (h : B → C) : A → C := h ∘ f

  --Postcomposition of arbitrary functions with f
  definition postcompose {A B : Type} (f : A → B) (C : Type) (l : C → A) : C → B := f ∘ l

  --Precomposing with an equivalence is an equivalence
  definition arrow_equiv_arrow_of_equiv_dom [instance] {A B : Type} (f : A → B) [F : funext] [Hf : is_equiv f] (C : Type)
      : is_equiv (precompose f C) :=
    adjointify (precompose f C) (λh, h ∘ f⁻¹)
      (λh, eq_of_homotopy (λx, ap h (sect f x)))
      (λg, eq_of_homotopy (λy, ap g (retr f y)))

  --Postcomposing with an equivalence is an equivalence
  definition arrow_equiv_arrow_of_equiv_cod [instance] {A B : Type} (f : A → B) [F : funext] [Hf : is_equiv f] (C : Type)
      : is_equiv (postcompose f C) :=
    adjointify (postcompose f C) (λl, f⁻¹ ∘ l)
      (λh, eq_of_homotopy (λx, retr f (h x)))
      (λg, eq_of_homotopy (λy, sect f (g y)))

  --Conversely, if pre- or post-composing with a function is always an equivalence,
  --then that function is also an equivalence.  It's convenient to know
  --that we only need to assume the equivalence when the other type is
  --the domain or the codomain.
  private definition isequiv_precompose_eq {A B : Type} (f : A → B) (C D : Type)
      (Ceq : is_equiv (precompose f C)) (Deq : is_equiv (precompose f D)) (k : C → D) (h : A → C) :
      k ∘ (precompose f C)⁻¹ h = (precompose f D)⁻¹ (k ∘ h) :=
    let invD := inv (precompose f D) in
    let invC := inv (precompose f C) in
    have eq1 : invD (k ∘ h) = k ∘ (invC h),
      from calc invD (k ∘ h) = invD (k ∘ (precompose f C (invC h))) : retr (precompose f C) h
		... = k ∘ (invC h) : !sect,
      eq1⁻¹

  definition is_equiv_of_is_equiv_precomp {A B : Type} (f : A → B) (Aeq : is_equiv (precompose f A))
      (Beq : is_equiv (precompose f B)) : (is_equiv f) :=
    let invA := inv (precompose f A) in
    let invB := inv (precompose f B) in
    let sect' : f ∘ (invA id) ∼ id  := (λx,
      calc f (invA id x) = (f ∘ invA id) x : idp
	... = invB (f ∘ id) x : apD10 (!isequiv_precompose_eq)
	... = invB (precompose f B id) x : idp
	... = x : apD10 (sect (precompose f B) id))
      in
    let retr' : (invA id) ∘ f ∼ id := (λx,
      calc invA id (f x) = precompose f A (invA id) x : idp
	... = x : apD10 (retr (precompose f A) id)) in
    adjointify f (invA id) sect' retr'

  end

end is_equiv

--Bundled versions of the previous theorems
namespace equiv

  definition arrow_equiv_arrow_of_equiv_dom [F : funext] {A B C : Type} {eqf : A ≃ B}
      : (B → C) ≃ (A → C) :=
    let f := to_fun eqf in
    let Hf := to_is_equiv eqf in
    equiv.mk (is_equiv.precompose f C)
      (@is_equiv.arrow_equiv_arrow_of_equiv_dom A B f F Hf C)

  definition arrow_equiv_arrow_of_equiv_cod [F : funext] {A B C : Type} {eqf : A ≃ B}
      : (C → A) ≃ (C → B) :=
    let f := to_fun eqf in
    let Hf := to_is_equiv eqf in
    equiv.mk (is_equiv.postcompose f C)
      (@is_equiv.arrow_equiv_arrow_of_equiv_cod A B f F Hf C)

end equiv
