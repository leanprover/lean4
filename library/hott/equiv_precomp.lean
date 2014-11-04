-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT
import .equiv .funext
open path function

namespace IsEquiv

  --If pre- or post-composing with a function is always an equivalence,
  --then that function is also an equivalence.  It's convenient to know
  --that we only need to assume the equivalence when the other type is
  --the domain or the codomain.
  context
  parameters {A B : Type} (f : A → B)

  definition precomp (C : Type) (h : B → C) : A → C := h ∘ f

  definition inv_precomp (C D : Type) (Ceq : IsEquiv (precomp C))
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
	... ≈ invB (f ∘ id) x : apD10 (!inv_precomp)
	... ≈ invB (precomp B id) x : idp
	... ≈ x : apD10 (sect (precomp B) id))
      in
    let retr' : Sect f (invA id) := (λx,
      calc invA id (f x) ≈ precomp A (invA id) x : idp
	... ≈ x : apD10 (retr (precomp A) id)) in
    adjointify f (invA id) sect' retr'

  end

end IsEquiv
