-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import .equiv .funext
open path function

namespace IsEquiv
  context
  parameters {A B : Type} (f : A → B)

  --Precomposition of arbitrary functions with f
  definition precomp (C : Type) (h : B → C) : A → C := h ∘ f

  --Postcomposition of arbitrary functions with f
  definition postcomp (C : Type) (l : C → A) : C → B := f ∘ l

  --Precomposing with an equivalence is an equivalence
  definition precompose [instance] [Hf : IsEquiv f] (C : Type):
      IsEquiv (precomp C) :=
    adjointify (precomp C) (λh, h ∘ f⁻¹)
      (λh, path_forall _ _ (λx, ap h (sect f x)))
      (λg, path_forall _ _ (λy, ap g (retr f y)))

  --Postcomposing with an equivalence is an equivalence
  definition postcompose [instance] [Hf : IsEquiv f] (C : Type):
      IsEquiv (postcomp C) :=
    adjointify (postcomp C) (λl, f⁻¹ ∘ l)
      (λh, path_forall _ _ (λx, retr f (h x)))
      (λg, path_forall _ _ (λy, sect f (g y)))

  --Conversely, if pre- or post-composing with a function is always an equivalence,
  --then that function is also an equivalence.  It's convenient to know
  --that we only need to assume the equivalence when the other type is
  --the domain or the codomain.
  private definition isequiv_precompose_eq (C D : Type) (Ceq : IsEquiv (precomp C))
      (Deq : IsEquiv (precomp D)) (k : C → D) (h : A → C) :
      k ∘ (inv (precomp C)) h ≈ (inv (precomp D)) (k ∘ h) :=
    let invD := inv (precomp D) in
    let invC := inv (precomp C) in
    have eq1 : invD (k ∘ h) ≈ k ∘ (invC h),
      from calc invD (k ∘ h) ≈ invD (k ∘ (precomp C (invC h))) : retr (precomp C) h
		... ≈ k ∘ (invC h) : !sect,
      eq1⁻¹

  definition isequiv_precompose (Aeq : IsEquiv (precomp A))
      (Beq : IsEquiv (precomp B)) : (IsEquiv f) :=
    let invA := inv (precomp A) in
    let invB := inv (precomp B) in
    let sect' : Sect (invA id) f := (λx,
      calc f (invA id x) ≈ (f ∘ invA id) x : idp
	... ≈ invB (f ∘ id) x : apD10 (!isequiv_precompose_eq)
	... ≈ invB (precomp B id) x : idp
	... ≈ x : apD10 (sect (precomp B) id))
      in
    let retr' : Sect f (invA id) := (λx,
      calc invA id (f x) ≈ precomp A (invA id) x : idp
	... ≈ x : apD10 (retr (precomp A) id)) in
    adjointify f (invA id) sect' retr'

  end

end IsEquiv

--Bundled versions of the previous theorems
namespace Equiv

  context
  parameters {A B C : Type} {eqf : A ≃ B}

  private definition f := equiv_fun eqf
  private definition Hf := equiv_isequiv eqf

  definition precompose : (B → C) ≃ (A → C) :=
    Equiv_mk (IsEquiv.precomp f C)
      (@IsEquiv.precompose A B f Hf C)

  definition postcompose : (C → A) ≃ (C → B) :=
    Equiv_mk (IsEquiv.postcomp f C)
      (@IsEquiv.postcompose A B f Hf C)

  end

end Equiv
